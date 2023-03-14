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

Search int bool.
  
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
