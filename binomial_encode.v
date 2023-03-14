Require Import Uint63 List.
Import ListNotations.

(* Compute C(m, n) *)
Fixpoint bin_compute m (n : nat) :=
  match n with 
  | S n1 => 
    match m with 
    | S m1 => (bin_compute m1 n1 + bin_compute m1 n)%uint63
    | 0   => 0%uint63
    end
  | 0    => 1%uint63
  end.

(* C(6,3) *)
Compute bin_compute 6 3.

(* l is a list of bool with exactly n true *)
Fixpoint bin_encode (l : list bool) (n : nat) :=
  match l with 
  | true :: l1 =>
     (bin_compute (length l1) n +  bin_encode l1 (Nat.pred n))%uint63
  | false :: l1 => bin_encode l1 n
  | nil => 0%uint63
  end.

(* Encoding 2 among 4 *)
Compute bin_compute 4 2.
(* there is 6 positions *)

Compute bin_encode [true; true; false; false] 2.
Compute bin_encode [true; false; true; false] 2.
Compute bin_encode [true; false; false; true] 2.
Compute bin_encode [false; true; true; false] 2.
Compute bin_encode [false; true; false; true] 2.
Compute bin_encode [false; false; true; true] 2.

Fixpoint bin_decode (m : nat) (n : nat) v : list bool :=
match m with 
| S m1 => if (leb (bin_compute m1 n) v) then
             true :: (bin_decode m1 (Nat.pred n) (v - bin_compute m1 n)%uint63)
          else false :: (bin_decode m1 n v)
| 0 => []
end.

Compute bin_decode 4 2 5%uint63.
Compute bin_decode 4 2 4%uint63.
Compute bin_decode 4 2 3%uint63.
Compute bin_decode 4 2 2%uint63.
Compute bin_decode 4 2 1%uint63.
Compute bin_decode 4 2 0%uint63.

(* Rotate 16 bits 90 degres counterclockwise *)

(* b0 b1 b2 b3 *)
(* b4 b5 b6 b7 *)
(* b8 b9 bA bB *)
(* bC bD bE bF *)

(* b3 b7 bB bF *)
(* b2 b6 bA bE *)
(* b1 b5 b9 bD *)
(* b0 b4 b8 bC *)

Definition rotate16_90 (l : list bool) := 
  match l with 
  | b0 :: b1 :: b2 :: b3 ::
    b4 :: b5 :: b6 :: b7 ::
    b8 :: b9 :: bA :: bB :: 
    bC :: bD :: bE :: bF :: nil =>
    b3 :: b7 :: bB :: bF ::
    b2 :: b6 :: bA :: bE ::
    b1 :: b5 :: b9 :: bD :: 
    b0 :: b4 :: b8 :: bC :: nil
    
  | _ => l
  end.

Definition rotate16_180 (l : list bool) := 
  rotate16_90 (rotate16_90 l).

Definition rotate16_270 (l : list bool) := 
  rotate16_90 (rotate16_180 l).

Lemma rotate16_360 l :  rotate16_90 (rotate16_270 l) = l.
Proof. do 17 (destruct l as [|? l]; simpl; auto). Qed.

(* Rotate 6 bits 90 degres counterclockwise *)

(**
       ---
       |b3|
     -------
    |b1|b0|b4|
     -------
       |b2|
       ---
       |b5|
*)

(**
       ---
       |b4|
     -------
    |b3|b0|b2|
     -------
       |b1|
       ---
       |b5|
*)

Definition rotate6_90 (l : list bool) :=
match l with 
  b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: nil => 
  b0 :: b3 :: b1 :: b4 :: b2 :: b5 :: nil
| _ => l
end.

Definition rotate6_180 (l : list bool) := 
  rotate6_90 (rotate6_90 l).

Definition rotate6_270 (l : list bool) := 
  rotate6_90 (rotate6_180 l).

Lemma rotate6_360 l :  rotate6_90 (rotate6_270 l) = l.
Proof. do 7 (destruct l as [|? l]; simpl; auto). Qed.

