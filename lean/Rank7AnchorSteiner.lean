import Rank7CharacterFourOrbits

namespace RankSeven.AnchorSteiner
open Pauli PauliEdgeBlocks HeavyPauliGroup CharacterFourOrbits StabilizerCosetTransform

variable {n : Nat} {G : MaximalFamily n} {T : Transversal G}
noncomputable local instance : DecidableEq (Word n) := Classical.typeDecidableEq _

/-- Character product one on the stabilizer, in the coset coordinates of an
arbitrary character transversal. All four arguments are actual character lines. -/
def plane (a r b c : Line T) :=
  wordAdd (wordAdd (wordAdd a.val r.val) b.val) c.val ∈ G.labels

theorem swapAnchorTriple (a r b c : Line T) : plane a r b c ↔ plane a b r c := by
  unfold plane
  rw [wordAddAssoc a.val r.val b.val,wordAddComm r.val b.val,←wordAddAssoc]

theorem swapTail (a r b c : Line T) : plane a r b c ↔ plane a r c b := by
  unfold plane
  rw [wordAddAssoc _ b.val c.val,wordAddComm b.val c.val,←wordAddAssoc]

theorem uniqueMate (a r b c y : Line T) (hc : plane a r b c) (hy : plane a r b y) :
    c=y := by
  let w:=wordAdd (wordAdd a.val r.val) b.val
  have together:=addMem G (wordAdd w c.val) (wordAdd w y.val) hc hy
  have ce : wordAdd (wordAdd w c.val) (wordAdd w y.val)=wordAdd c.val y.val := by
    rw [wordAddComm w c.val,←wordAddAssoc,wordAddCancel]
  rw [ce] at together
  exact Subtype.ext (T.separated _ c.property _ y.property together)

def row (p : α → Bool) : List α → Nat
  | [] => 0
  | b::bs => (if p b then 1 else 0)+row p bs
def pairs (p : α → α → Bool) : List α → Nat
  | [] => 0
  | b::bs => row (p b) bs + pairs p bs
def triples (p : α → α → α → Bool) : List α → Nat
  | [] => 0
  | b::bs => pairs (p b) bs + triples p bs
def degree (p : α → α → Bool) (target : List α) : List α → Nat
  | [] => 0
  | b::bs => row (p b) target + degree p target bs

private theorem rowZero {p : α → Bool} {xs : List α} (h : ∀ x ∈ xs, p x=false) : row p xs=0 := by
  induction xs with
  | nil => rfl
  | cons b bs ih => simp [row,h b List.mem_cons_self,ih (fun x hx=> h x (List.mem_cons_of_mem _ hx))]

private theorem rowOne (p : α → Bool) (unique : ∀ u v, p u=true → p v=true → u=v)
    (xs : List α) (nd : xs.Nodup) : row p xs ≤ 1 := by
  induction xs with
  | nil => simp [row]
  | cons b bs ih =>
    obtain ⟨out,tail⟩ := List.nodup_cons.mp nd
    cases hb : p b with
    | false => simpa [row,hb] using ih tail
    | true =>
      have zero : row p bs=0 := rowZero (fun y hy => by
        cases e : p y
        · rfl
        · exact False.elim (out ((unique y b e hb) ▸ hy)))
      simp [row,hb,zero]

private theorem degreeMore (p : α → α → Bool) (symm : ∀u v, p u v=p v u)
    (b : α) (xs ys : List α) :
    degree p (b::xs) ys = row (p b) ys + degree p xs ys := by
  induction ys with
  | nil => rfl
  | cons c cs ih => simp only [degree,row,ih,symm c b]; omega

private theorem doublePairs (p : α → α → Bool) (symm : ∀u v,p u v=p v u) (xs : List α) :
    2*pairs p xs ≤ degree p xs xs := by
  induction xs with
  | nil => simp [pairs,degree]
  | cons b bs ih => simp only [pairs,degree,row,degreeMore p symm]; omega

private theorem degreeBound (p : α → α → Bool)
    (unique : ∀ b u v,p b u=true → p b v=true → u=v) (xs : List α) (nd : xs.Nodup) (ys : List α) :
    degree p xs ys≤ys.length := by
  induction ys with
  | nil => simp [degree]
  | cons y ys ih =>
    have h:=rowOne _ (unique y) xs nd
    simp only [degree,List.length_cons]; omega

theorem pairsBound (p : α → α → Bool) (symm : ∀u v,p u v=p v u)
    (unique : ∀ b u v,p b u=true → p b v=true → u=v) (xs : List α) (nd : xs.Nodup) :
    2*pairs p xs≤xs.length := Nat.le_trans (doublePairs p symm xs) (degreeBound p unique xs nd xs)

noncomputable def hit (a r b c : Line T) : Bool := @decide (plane a r b c) (Classical.propDecidable _)
private theorem hitProp (a r b c : Line T) : hit a r b c = true ↔ plane a r b c := @decide_eq_true_eq (plane a r b c) (Classical.propDecidable _) |> Iff.of_eq
private theorem eqHitBool {u v : Bool} (h : u=true ↔ v=true) : u=v := by cases u <;> cases v <;> simp_all
noncomputable def score (a : Line T) := triples (hit a)

theorem addedAtHead (a r : Line T) (xs : List (Line T)) (nd : xs.Nodup) :
    score a (r::xs) ≤ score a xs + xs.length/2 := by
  have symm (u v : Line T) : hit a r u v=hit a r v u :=
    by apply eqHitBool; rw [hitProp,hitProp]; exact swapTail a r u v
  have unique (b u v : Line T) (hu : hit a r b u=true) (hv : hit a r b v=true) : u=v :=
    uniqueMate a r b u v ((hitProp _ _ _ _).mp hu) ((hitProp _ _ _ _).mp hv)
  have bound := pairsBound _ symm unique xs nd
  change pairs (hit a r) xs + triples (hit a) xs ≤ triples (hit a) xs + xs.length/2
  omega

private theorem rowPerm {x y : List α} (h : x.Perm y) (p : α → Bool) : row p x=row p y := by
  induction h with
  | nil => rfl
  | cons z _ ih => simp [row,ih]
  | swap u v w => simp only [row]; omega
  | trans _ _ ih ij => exact ih.trans ij

private theorem pairsPerm (p : α → α → Bool) (symm : ∀u v,p u v=p v u) {xs ys : List α}
    (h : xs.Perm ys) : pairs p xs=pairs p ys := by
  induction h with
  | nil => rfl
  | cons z h ih => simp [pairs,ih,rowPerm h]
  | swap u v w => simp only [pairs,row,symm u v]; omega
  | trans _ _ ih ij => exact ih.trans ij

theorem scorePerm (a : Line T) {xs ys : List (Line T)} (h : xs.Perm ys) : score a xs=score a ys := by
  have swap (r u v : Line T) : hit a r u v=hit a r v u := by apply eqHitBool; rw [hitProp,hitProp]; exact swapTail a r u v
  unfold score
  induction h with
  | nil => rfl
  | cons z h ih => simp only [triples,pairsPerm (hit a z) (swap z) h,ih]
  | swap u v w =>
    have e : hit a u v=hit a v u := funext (fun c=>by apply eqHitBool; rw [hitProp,hitProp]; exact swapAnchorTriple a u v c)
    simp only [triples,pairs,e]; omega
  | trans _ _ ih ij => exact ih.trans ij

theorem insertion (a r : Line T) {xs ys : List (Line T)} (related : ys.Perm (r::xs)) (nd : xs.Nodup) :
    score a ys ≤ score a xs + xs.length/2 :=
  (scorePerm a related).symm ▸ addedAtHead a r xs nd

end RankSeven.AnchorSteiner
#print axioms RankSeven.AnchorSteiner.insertion
