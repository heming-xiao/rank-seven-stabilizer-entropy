import Rank7SlaterAlternant

/-! Positivity of the tensor projection union bound and its evaluation on
the top Slater source. -/
namespace RankSeven.SlaterUnionBound
open Lean.Grind Pauli ComplexScalar OddTensorUncertainty SlaterAlternant
open PhysicalPairedReduction (dagger)
open PauliPairContraction (image normSum)
variable {R α β γ : Type} [CommRing R]

abbrev Mx (α R : Type) := α → α → ComplexScalar R

def ident [DecidableEq α] (i j : α) : ComplexScalar R := if i=j then 1 else 0

def Gram (G : Mx α R) : Prop :=
  ∃ (ι : Type) (rows : List ι) (F : ι → α → ComplexScalar R),G=matMul rows (dagger F) F

theorem gramZero : Gram (fun _ _ : α => (0:ComplexScalar R)) :=
  ⟨Unit,[],fun _ _ => 0,rfl⟩

private theorem sumAppend {C δ : Type} [CommRing C] (xs ys : List δ) (f : δ → C) :
    sumOver (xs++ys) f=sumOver xs f+sumOver ys f := by
  induction xs with
  | nil => simp [sumOver]; grind only
  | cons i xs ih => simp only [List.cons_append,sumOver,List.map_cons,List.sum_cons] at *; grind only

theorem gramAdd {G1 G2 : Mx α R} (g1 : Gram G1) (g2 : Gram G2) : Gram (fun i j => G1 i j+G2 i j) := by
  obtain ⟨a,xs,A,rfl⟩ := g1; obtain ⟨b,ys,B,rfl⟩ := g2
  let F : Sum a b → α → ComplexScalar R := Sum.elim A B
  refine ⟨Sum a b,xs.map Sum.inl++ys.map Sum.inr,F,?_⟩
  funext i j
  change _=sumOver _ (fun k => star (F k i)*F k j)
  rw [sumAppend]; simp only [sumOver,List.map_map,Function.comp_def]; rfl

theorem gramTensor {G : Mx α R} {H : Mx β R} (g : Gram G) (h : Gram H) : Gram (tensor G H) := by
  obtain ⟨a,xs,A,rfl⟩ := g; obtain ⟨b,ys,B,rfl⟩ := h
  refine ⟨a×b,productIndices xs ys,tensor A B,?_⟩
  rw [tensorMatMul]; congr 1
  funext i j; exact (star_mul (A j.1 i.1) (B j.2 i.2)).symm

theorem gramIdentity [DecidableEq α] (xs : List α) (nd : xs.Nodup) (full : ∀ i,i∈xs) : Gram (ident (R:=R) (α:=α)) := by
  refine ⟨α,xs,ident,?_⟩
  funext i j; change ident i j=sumOver xs (fun k => star (ident k i)*ident k j)
  rw [←ExteriorPauliBase.sumOnIndex xs i (fun k => ident (R:=R) k j) nd (full i)]
  apply sumOverCongr; intro k
  have so : star (1:ComplexScalar R)=1 := by apply ComplexScalar.ext <;> simp <;> grind only
  have sz : star (0:ComplexScalar R)=0 := by apply ComplexScalar.ext <;> simp <;> grind only
  by_cases eq : i=k
  · subst k; simp only [ident,ite_true,so,Semiring.one_mul]
  · have z : k≠i := fun e => eq e.symm
    simp only [ident,eq,z,ite_false,sz,Semiring.zero_mul]

def derivative {C α β : Type} [CommRing C] (A B : α → β → C) : (r : Nat) → Sites α r → Sites β r → C
  | 0,_,_ => 0
  | r+1,i,j => B i.1 j.1*matrix A r i.2 j.2+A i.1 j.1*derivative A B r i.2 j.2

/-- If G and I-G are Gram matrices, then both I^⊗m-G^⊗m and the
excess of the sum of single-leg losses over this total loss are Gram
matrices, in every tensor degree. -/
theorem tensorUnion {I G : Mx α R} (gi : Gram I) (gg : Gram G) (gb : Gram (fun i j => I i j-G i j))
    (r : Nat) :
    Gram (fun x y => matrix I r x y-matrix G r x y) ∧
    Gram (fun x y => derivative I (fun i j => I i j-G i j) r x y-matrix I r x y+matrix G r x y) := by
  let B i j := I i j-G i j
  have power (r : Nat) : Gram (matrix I r) := by
    induction r with
    | zero =>
      refine ⟨Unit,[()],fun _ _ => 1,?_⟩; funext x y
      change (1:ComplexScalar R)=star 1*1+0; apply ComplexScalar.ext <;> simp <;> grind only
    | succ r ih => exact gramTensor gi ih
  induction r with
  | zero =>
    have one : (fun x y : Sites α 0 => matrix I 0 x y-matrix G 0 x y)=(fun _ _ => 0) := by funext x y; change (1:ComplexScalar R)-1=0; grind only
    have two : (fun x y : Sites α 0 => derivative I B 0 x y-matrix I 0 x y+matrix G 0 x y)=(fun _ _ => 0) := by
      funext x y; change (0:ComplexScalar R)-1+1=0; grind only
    change _ ∧ Gram (fun x y => derivative I B 0 x y-matrix I 0 x y+matrix G 0 x y)
    rw [one,two]; exact ⟨gramZero,gramZero⟩
  | succ r ih =>
    let E x y := matrix I r x y-matrix G r x y
    let D x y := derivative I B r x y-matrix I r x y+matrix G r x y
    have gE : Gram E := ih.1; have gD : Gram D := ih.2
    have a := gramAdd (gramTensor gb (power r)) (gramTensor gg gE)
    have b := gramAdd (gramTensor gi gD) (gramTensor gb gE)
    have first : (fun x y => matrix I (r+1) x y-matrix G (r+1) x y)=
        (fun x y => tensor B (matrix I r) x y+tensor G E x y) := by
      funext x y; dsimp only [matrix,tensor,B,E]; grind only
    have second : (fun x y => derivative I B (r+1) x y-matrix I (r+1) x y+matrix G (r+1) x y)=
        (fun x y => tensor I D x y+tensor B E x y) := by
      funext x y; dsimp only [derivative,matrix,tensor,B,E,D]; grind only
    change _ ∧ Gram (fun x y => derivative I B (r+1) x y-matrix I (r+1) x y+matrix G (r+1) x y)
    rw [first,second]; exact ⟨a,b⟩

def energy (xs : List α) (M : Mx α R) (z : α → ComplexScalar R) :=
  let Z (i : α) (_ : Unit) := z i
  (matMul xs (dagger Z) (matMul xs M Z) () ()).re

private theorem reSum {a : Type} (xs : List a) (f : a → ComplexScalar R) :
    (sumOver xs f).re=sumOver xs (fun i => (f i).re) := by
  induction xs with
  | nil => rfl
  | cons u xs ih => change (f u+sumOver xs f).re=_; rw [re_add,ih]; rfl

theorem energyGram {a : Type} (xs : List α) (rows : List a) (F : a → α → ComplexScalar R) (z : α → ComplexScalar R) :
    energy xs (matMul rows (dagger F) F) z=normSum rows (image xs F z) := by
  let Z (i : α) (_ : Unit) := z i
  let V := matMul xs F Z
  have e : matMul xs (dagger Z) (matMul xs (matMul rows (dagger F) F) Z)=matMul rows (dagger V) V := by
    unfold V; rw [PhysicalPairedReduction.daggerProduct]; simp only [matMulAssoc]
  unfold energy; change (matMul xs (dagger Z) (matMul xs (matMul rows (dagger F) F) Z) () ()).re=_
  rw [e]; change (sumOver rows (fun a => star (V a ())*V a ())).re=_
  rw [reSum]; simp only [re_star_mul_self]; rfl

theorem energyNonnegative [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]
    (xs : List α) {M : Mx α R} (gram : Gram M) (z : α → ComplexScalar R) : 0≤energy xs M z := by
  obtain ⟨a,rows,F,rfl⟩ := gram; rw [energyGram]
  exact Compression.sumOverNonnegative rows _ (fun i _ => normSq_nonnegative _)

theorem energySubAdd (xs : List α) (A B C : Mx α R) (z : α → ComplexScalar R) :
    energy xs (fun i j => A i j-B i j+C i j) z=energy xs A z-energy xs B z+energy xs C z := by
  have point (i j) : (A i j-B i j+C i j)*z j=A i j*z j-B i j*z j+C i j*z j := by grind only
  have out (v a b c : ComplexScalar R) : v*(a-b+c)=v*a-v*b+v*c := by grind only
  unfold energy; dsimp only [matMul,dagger]
  simp only [point,sumOverAdd,Compression.sumOverSub,out,re_add,re_sub]

private theorem ifIndex [DecidableEq α] (xs : List α) (nd : xs.Nodup) (full : ∀ i,i∈xs) (i : α) (f : α→ComplexScalar R) :
    sumOver xs (fun j => ident i j*f j)=f i := by
  rw [←ExteriorPauliBase.sumOnIndex xs i f nd (full i)]
  apply sumOverCongr; intro j; by_cases h : i=j <;> simp only [ident,h,ite_true,ite_false,Semiring.one_mul,Semiring.zero_mul]

theorem energyEigen (xs : List α) (M : Mx α R) (z : α → ComplexScalar R) (c : ComplexScalar R)
    (eigen : ∀ i∈xs, z i≠0 → image xs M z i=z i*c) :
    energy xs M z=normSum xs z*c.re := by
  unfold energy; change (sumOver xs (fun i => star (z i)*image xs M z i)).re=_
  rw [reSum]
  change _=sumOver xs (fun i => normSq (z i))*c.re
  rw [sumOverMulRight]
  unfold sumOver; congr 1; apply List.map_congr_left; intro i hi
  by_cases h : z i=0
  · rw [h,normSq_zero]; simp only [Semiring.zero_mul]
    have e : star (0:ComplexScalar R)=0 := by apply ComplexScalar.ext <;> simp <;> grind only
    rw [e,Semiring.zero_mul,re_zero]
  · rw [eigen i hi h,←Semiring.mul_assoc,star_mul_self]
    simp only [re_mul,re_ofReal,im_ofReal,Semiring.zero_mul]; grind only

theorem energyIdentity [DecidableEq α] (xs : List α) (nd : xs.Nodup) (full : ∀ i,i∈xs) (z : α → ComplexScalar R) :
    energy xs ident z=normSum xs z := by
  have h := energyEigen xs ident z 1 (fun i _ _ => (ifIndex xs nd full i z).trans (Semiring.mul_one _).symm)
  simpa only [re_one,Semiring.mul_one] using h

theorem matrixIdent [DecidableEq α] (r : Nat) : matrix (ident (R:=R) (α:=α)) r=ident := by
  funext x y; exact matrixIdentity r x y

private theorem derivDiag [DecidableEq α] (B : Mx α R) (r : Nat) (x : Sites α r) :
    derivative ident B r x x=sumOver (tupleList r x) (fun a => B a a) := by
  induction r with
  | zero => rfl
  | succ r ih =>
    change B x.1 x.1*matrix ident r x.2 x.2+ident x.1 x.1*derivative ident B r x.2 x.2=B x.1 x.1+_
    rw [matrixIdent,ih]; simp only [ident,ite_true,Semiring.mul_one,Semiring.one_mul]; rfl

private theorem derivOff [DecidableEq α] (B : Mx α R) (r : Nat) (x y : Sites α r) (ne : x≠y)
    (perm : (tupleList r x).Perm (tupleList r y)) : derivative ident B r x y=0 := by
  induction r with
  | zero => cases x; cases y; contradiction
  | succ r ih =>
    obtain ⟨a,x⟩ := x; obtain ⟨b,y⟩ := y
    change (a::tupleList r x).Perm (b::tupleList r y) at perm
    change B a b*matrix ident r x y+ident a b*derivative ident B r x y=0
    rw [matrixIdent]
    by_cases eq : a=b
    · subst b
      have bad : x≠y := fun h => ne (h ▸ rfl)
      rw [ih x y bad perm.cons_inv]; simp [ident,bad] <;> grind only
    · have bad : x≠y := by
        intro h; subst y; have c := List.perm_iff_count.mp perm a
        simp [show b≠a from fun k => eq k.symm] at c
      simp [ident,eq,bad] <;> grind only

private theorem sumPerm {δ : Type} {xs ys : List δ} (p : xs.Perm ys) (f : δ → ComplexScalar R) : sumOver xs f=sumOver ys f := by
  induction p with
  | nil => rfl
  | cons a p ih => exact congrArg (fun y => f a+y) ih
  | swap a b xs => change f b+(f a+_)=f a+(f b+_); grind only
  | trans _ _ ih jh => exact ih.trans jh

private theorem permutationOfFull {δ : Type} [DecidableEq δ] (xs ys : List δ) (nd : xs.Nodup) (len : xs.length=ys.length)
    (sub : xs⊆ys) : xs.Perm ys := by
  induction xs generalizing ys with
  | nil => have z := List.length_eq_zero_iff.mp len.symm; rw [z]
  | cons a xs ih =>
    have h := List.nodup_cons.mp nd
    have p := List.perm_cons_erase (sub (a:=a) List.mem_cons_self)
    have l := p.length_eq
    have s : xs⊆ys.erase a := by
      intro b hb; have w := p.mem_iff.mp (sub (List.mem_cons_of_mem a hb))
      exact (List.mem_cons.mp w).elim (fun e => False.elim (h.1 (e ▸ hb))) id
    exact (List.Perm.cons a (ih _ h.2 (by simp only [List.length_cons] at len l; omega) s)).trans p.symm

section Order
variable [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]

theorem slaterPermutation (m : Nat) (x : Sites (Fin m) m) (nonzero : slater (C:=ComplexScalar R) m x≠0) :
    (tupleList m x).Perm (List.finRange m) := by
  have cancel (z : ComplexScalar R) (h : z= -z) : z=0 := by
    have a := congrArg ComplexScalar.re h; have b := congrArg ComplexScalar.im h
    simp only [re_neg,im_neg] at a b; apply ComplexScalar.ext <;> change _=0 <;> grind only
  have distinct (xs : List (Fin m)) : ∀ pre : List (Fin m),orientation (C:=ComplexScalar R) (pre++xs)≠0 → xs.Nodup := by
    induction xs with
    | nil => exact fun _ _ => List.nodup_nil
    | cons a xs ih =>
      intro pre nz
      refine List.nodup_cons.mpr ⟨?_,ih (pre++[a]) (by simpa only [List.append_assoc,List.singleton_append] using nz)⟩
      intro mem; have p := (List.Perm.cons a (List.perm_cons_erase mem)).symm
      have alt := orientationAlt (C:=ComplexScalar R) m
      exact nz (permZero _ alt p pre (cancel _ (alt pre a a (xs.erase a))))
  exact permutationOfFull _ _ (distinct _ [] nonzero) (by rw [tupleLength,List.length_finRange]) (fun _ _ => List.mem_finRange _)

/-- The sum of all one-particle marginals of the top Slater state is its
mass times the source trace. The combinatorics uses no factorial count. -/
theorem marginalTrace (B : Mx (Fin m) R) :
    let xs := indices (List.finRange m) m
    let z := slater (C:=ComplexScalar R) m
    energy xs (derivative ident B m) z=normSum xs z*(trace (List.finRange m) B).re := by
  let xs := indices (List.finRange m) m
  let z := slater (C:=ComplexScalar R) m
  apply energyEigen
  intro i hi nz
  have pi := slaterPermutation m i nz
  let T := trace (List.finRange m) B
  have ds : derivative ident B m i i=T := (derivDiag B m i).trans (sumPerm pi _)
  have e := ExteriorPauliBase.sumOnIndex xs i (fun j => z j*T) (indicesNodup _ (List.nodup_finRange _) _) hi
  change sumOver xs (fun j => derivative ident B m i j*z j)=z i*T; rw [←e]
  apply sumOverCongr; intro j
  by_cases h : i=j
  · subst j; rw [ds]; simp only [ite_true]; grind only
  · rw [ite_eq_right h]
    by_cases u : z j=0
    · rw [u,Semiring.mul_zero]
    · rw [derivOff B m i j h (pi.trans (slaterPermutation m j u).symm),Semiring.zero_mul]
/-- The determinant of a complex square contraction controls the total
one-particle leakage. The Gram certificate of I−H†H suffices, including
for singular matrices and zero determinant. -/
theorem determinantLeakage (m : Nat) (H : Mx (Fin m) R)
    (complement : Gram (fun i j => ident i j-matMul (List.finRange m) (dagger H) H i j)) :
    1-(trace (List.finRange m) (fun i j => ident i j-matMul (List.finRange m) (dagger H) H i j)).re≤normSq (determinant m H) := by
  let src := List.finRange m
  let ts := indices src m
  let I : Mx (Fin m) R := ident
  let G := matMul src (dagger H) H
  let B i j := I i j-G i j
  let z := slater (C:=ComplexScalar R) m
  let mass := normSum ts z
  let d := determinant m H
  have gi : Gram I := gramIdentity src (List.nodup_finRange m) (fun i => List.mem_finRange i)
  have gg : Gram G := ⟨Fin m,src,H,rfl⟩
  have u := (tensorUnion gi gg complement m).2
  have e := energyNonnegative ts u z
  change 0≤energy ts (fun i j => derivative I B m i j-matrix I m i j+matrix G m i j) z at e
  rw [energySubAdd] at e
  have single : energy ts (derivative I B m) z=mass*(trace src B).re := marginalTrace B
  have all : energy ts (matrix I m) z=mass := by
    rw [matrixIdent]; exact energyIdentity ts (indicesNodup src (List.nodup_finRange m) m) (indicesFull src (fun i => List.mem_finRange i) m) z
  have prod : matrix G m=matMul ts (dagger (matrix H m)) (matrix H m) := by rw [matrixDagger,matrixComp]
  have traceG : energy ts (matrix G m) z=mass*normSq d := by
    rw [prod,energyGram]; change sumOver ts (fun i => normSq (image ts (matrix H m) z i))=(sumOver ts (fun i => normSq (z i)))*normSq d
    rw [sumOverMulRight]; apply sumOverCongr; intro i
    have eq : image ts (matrix H m) z i=z i*d := topEigenvector m H i
    rw [eq,normSq_mul]
  rw [single,all,traceG] at e
  have pos : 0<mass := slaterMassPositive m
  change 1-(trace src B).re≤normSq d
  apply Classical.byContradiction; intro no
  have bad := OrderedRing.mul_pos pos (show 0<1-(trace src B).re-normSq d by grind only)
  grind only
end Order

end RankSeven.SlaterUnionBound

#print axioms RankSeven.SlaterUnionBound.tensorUnion
#print axioms RankSeven.SlaterUnionBound.energyNonnegative
#print axioms RankSeven.SlaterUnionBound.slaterPermutation
#print axioms RankSeven.SlaterUnionBound.marginalTrace
#print axioms RankSeven.SlaterUnionBound.determinantLeakage

