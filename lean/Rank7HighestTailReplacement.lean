import Rank7AnchorTripleEnergy

namespace RankSeven.HighestTailReplacement

open Lean.Grind Pauli ComplexScalar AnchorSteinerTest AnchorExteriorCreation AnchorExteriorFive AnchorMixedCAR AnchorTripleEnergy
variable {R I : Type} [CommRing R]
local notation "C" => ComplexScalar R

abbrev energy {d : Nat} (f : Basis d→C) : R := mass (qubitIndices d) f
abbrev modeMass (L : List I) (y : I→C) : R := sumOver L (fun i=>normSq (y i))

private theorem raiseLinear (L : List I) (y : I→C) (a b : C) (f g : Basis L.length→C) :
    raise y L (fun z=>a*f z+b*g z)=fun z=>a*raise y L f z+b*raise y L g z :=
  funext (linearRaise y L a b f g)

private theorem lowerLinear (L : List I) (y : I→C) (a b : C) (f g : Basis L.length→C) :
    lower y L (fun z=>a*f z+b*g z)=fun z=>a*lower y L f z+b*lower y L g z :=
  funext (linearLower y L a b f g)

theorem raiseSquare (L : List I) (y : I→C) (f : Basis L.length→C) :
    raise y L (raise y L f)=fun _=>0 := by
  induction L with
  | nil => rfl
  | cons i L ih =>
    funext ⟨j,z⟩; cases j
    · exact congrFun (ih (fun u=>f (false,u))) z
    · simp only [raise]
      have e (u : Basis L.length) : y i * f (false,u)-raise y L (fun w=>f (true,w)) u =
          y i*f (false,u)+(-1)*raise y L (fun w=>f (true,w)) u := by grind only
      rw [funext e,raiseLinear L y (y i) (-1) (fun u=>f (false,u)) (raise y L (fun u=>f (true,u))),ih]
      grind only

theorem lowerSquare (L : List I) (y : I→C) (f : Basis L.length→C) :
    lower y L (lower y L f)=fun _=>0 := by
  induction L with
  | nil => rfl
  | cons i L ih =>
    funext ⟨j,z⟩; cases j
    · simp only [lower]
      have e (u : Basis L.length) : star (y i)*f (true,u)+lower y L (fun w=>f (false,w)) u =
          star (y i)*f (true,u)+1*lower y L (fun w=>f (false,w)) u := by grind only
      rw [funext e,lowerLinear L y (star (y i)) 1 (fun u=>f (true,u)) (lower y L (fun u=>f (false,u))),ih]
      grind only
    · simp only [lower]
      have e (u : Basis L.length) : -lower y L (fun w=>f (true,w)) u =
          (-1)*lower y L (fun w=>f (true,w)) u+0*f (true,u) := by grind only
      rw [funext e,lowerLinear L y (-1) 0 (lower y L (fun u=>f (true,u))) (fun u=>f (true,u)),ih]
      grind only

theorem energyZero (d : Nat) : energy (R:=R) (d:=d) (fun _=>0)=0 := by
  change sumOver (qubitIndices d) (fun _=>normSq (0:C))=0
  have e : normSq (0:C)=0 := by simp only [normSq,re_zero,im_zero]; grind only
  rw [e]
  generalize qubitIndices d=B
  induction B with
  | nil => rfl
  | cons i B ih => change 0+sumOver B _=0; rw [ih]; grind only

theorem energyCAR (L : List I) (y : I→C) (f : Basis L.length→C) :
    energy (raise y L f)+energy (lower y L f)=modeMass L y*energy f := by
  have h:=congrArg ComplexScalar.re (carGram y L f f)
  simp only [re_add,reGram,re_mul,im_ofReal,re_ofReal] at h
  change mass _ _+mass _ _=sumOver _ _*mass _ _; grind only

/-- The two vacancy-sector vectors give an exact division-free energy decomposition. -/
theorem energyReplacement (L : List I) (y : I→C) (f : Basis L.length→C) :
    modeMass L y*modeMass L y*energy f=
      energy (lower y L (raise y L f))+modeMass L y*energy (lower y L f) := by
  have a:=energyCAR L y f
  have b:=energyCAR L y (raise y L f)
  rw [raiseSquare,energyZero] at b
  grind only

theorem contractedRaise (L : List I) (y a b c : I→C) (f : Basis L.length→C) :
    contracted L y a b c (raise y L f)=raise y L (contracted L y a b c f) := by
  have ii:=triplePush L y a b c (raise y L f)
  rw [raiseSquare] at ii
  have form : three L a b c (raise y L f)=fun z=>1*contracted L y a b c f z+
      (-1)*raise y L (three L a b c f) z := by
    funext z; rw [triplePush]; grind only
  rw [form,raiseLinear,raiseSquare] at ii
  unfold three at ii
  simp only [zeroLower] at ii
  funext z; have h:=ii z; grind only

theorem testReplacement (L : List I) (y a b c : I→C) (f : Basis L.length→C) :
    modeMass L y*modeMass L y*energy (contracted L y a b c f)=
      energy (contracted L y a b c (lower y L (raise y L f)))+
      modeMass L y*energy (contracted L y a b c (lower y L f)) := by
  have h:=energyReplacement L y (contracted L y a b c f)
  rw [←contractedRaise,funext (contractedLower L y a b c _),funext (contractedLower L y a b c _)] at h
  exact h

theorem lowerLocal (y : I→C) (L : List I) (f g : Basis L.length→C) (U : Basis L.length)
    (h : ∀r : I,∀S : Basis L.length,(occupied L S).Perm (r::occupied L U) → f S=g S) :
    lower y L f U=lower y L g U := by
  induction L with
  | nil => rfl
  | cons i L ih =>
    rcases U with ⟨b,z⟩; cases b
    · have same:=h i (true,z) (List.Perm.refl _)
      have rest:=ih (fun w=>f (false,w)) (fun w=>g (false,w)) z (fun r S hs=>h r (false,S) hs)
      change star (y i)*f (true,z)+_ = star (y i)*g (true,z)+_; rw [same,rest]
    · have rest:=ih (fun w=>f (true,w)) (fun w=>g (true,w)) z (fun r S hs=>h r (true,S)
        ((hs.cons i).trans (List.Perm.swap r i _)))
      change -_ = -_; rw [rest]

theorem raiseZero (L : List I) (y : I→C) : raise y L (fun _=>0)=fun _=>0 := by
  funext z; induction L with
  | nil => rfl
  | cons i L ih => rcases z with ⟨b,z⟩; cases b <;> simp only [raise,ih] <;> grind only

def cap (L : List I) (k : Nat) (f : Basis L.length→C) : Prop :=
  ∀ S, f S≠0 → (occupied L S).length≤k

theorem capRaise (L : List I) (k : Nat) (y : I→C) (f : Basis L.length→C)
    (hf : cap L k f) : cap L (k+1) (raise y L f) := by
  intro U nz; apply Classical.byContradiction; intro bad
  apply nz
  rw [←congrFun (raiseZero L y) U]
  apply raiseLocal; intro r S hs
  apply Classical.byContradiction; intro ns
  have hc:=hf S ns; have eq:=hs.length_eq
  simp only [List.length_cons] at eq; omega

theorem capLower (L : List I) (k : Nat) (y : I→C) (f : Basis L.length→C)
    (hf : cap L (k+1) f) : cap L k (lower y L f) := by
  intro U nz; apply Classical.byContradiction; intro bad
  apply nz
  rw [←congrFun (zeroLower y L) U]
  apply lowerLocal; intro r S hs
  apply Classical.byContradiction; intro ns
  have hc:=hf S ns; have eq:=hs.length_eq
  simp only [List.length_cons] at eq; omega

/-- A bound on y-vacant states suffices for an arbitrary tail state of degree at most
five, even when the tail modes overlap y. Each row is the physical contracted triple. -/
theorem vacantSuffices {J : Type} (L : List I) (y : I→C) (T : List J) (a b c : J→I→C)
    (f : Basis L.length→C) (hf : cap L 5 f)
    [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]
    (hn : 0<modeMass L y)
    (vacant : ∀g : Basis L.length→C, cap L 5 g → lower y L g=(fun _=>0) →
      sumOver T (fun t=>energy (contracted L y (a t) (b t) (c t) g))≤2*modeMass L y*energy g) :
    sumOver T (fun t=>energy (contracted L y (a t) (b t) (c t) f))≤2*modeMass L y*energy f := by
  let u:=lower y L (raise y L f)
  let w:=lower y L f
  let n:=modeMass L y
  let cost (g : Basis L.length→C):=sumOver T fun t=>energy (contracted L y (a t) (b t) (c t) g)
  have hu : cap L 5 u:=capLower L 5 y _ (capRaise L 5 y f hf)
  have hw : cap L 4 w:=capLower L 4 y f hf
  have hu' := vacant u hu (lowerSquare L y _)
  have hw' := vacant w (fun S nz=>Nat.le_trans (hw S nz) (by decide)) (lowerSquare L y _)
  change cost u≤2*n*energy u at hu'
  change cost w≤2*n*energy w at hw'
  have eq : n*n*cost f=cost u+n*cost w := by
    unfold cost; rw [sumOverMulLeft T _ (n*n),sumOverMulLeft T _ n,←sumOverAdd]; apply sumOverCongr
    intro t; exact testReplacement L y (a t) (b t) (c t) f
  have ee:=energyReplacement L y f
  change n*n*energy f=energy u+n*energy w at ee
  change 0<n at hn
  have ee' : n*n*(2*n*energy f)=2*n*energy u+n*(2*n*energy w) := by grind only
  have mul:=OrderedRing.mul_le_mul_of_nonneg_left hw' (Std.le_of_lt hn)
  have h : n*n*cost f ≤ n*n*(2*n*energy f) := by grind only
  have nn : 0<n*n:=OrderedRing.mul_pos hn hn
  change cost f≤2*n*energy f
  apply Classical.byContradiction; intro neg
  have strict : 2*n*energy f<cost f:=by grind only
  have bad := OrderedRing.mul_lt_mul_of_pos_left strict nn
  grind only

end RankSeven.HighestTailReplacement

#print axioms RankSeven.HighestTailReplacement.energyReplacement
#print axioms RankSeven.HighestTailReplacement.contractedRaise
#print axioms RankSeven.HighestTailReplacement.testReplacement
#print axioms RankSeven.HighestTailReplacement.capRaise
#print axioms RankSeven.HighestTailReplacement.capLower
#print axioms RankSeven.HighestTailReplacement.vacantSuffices

