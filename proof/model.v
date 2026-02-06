From LAProof.accuracy_proofs Require Import preamble common float_acc_lems mv_mathcomp solve_model.


Section WithNaN.

Variable NAN: FPCore.Nans.
Variable t: type.

Definition ord_enum2 m n : seq ('I_m * 'I_n) :=
  flatten (map (fun i => map (fun j => (i,j)) (ord_enum n)) (ord_enum m)). 

Definition point_mx [T] (zero: T) [m n] (i: 'I_m) (j: 'I_n) (x: T) : 'M[T]_(m,n):=
   \matrix_(i',j') if (i'==i) && (j'==j) then x else zero.

Definition matrix_add_to [n] (A: 'M[ftype t]_n) [ne] (ids: 'I_n ^ ne) (B: 'M[ftype t]_ne) : 
                       'M[ftype t]_n :=
 foldl (@F.addmx _ _ n n) A (map (fun '(i,j) => point_mx (Zconst t 0) (ids i) (ids j) (B i j)) (ord_enum2 ne ne)).

End WithNaN.
