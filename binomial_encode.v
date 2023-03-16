Require Import cube_explore Uint63 List.
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

(* position x : {0 .. 7} y : {0 ...7}*)

Definition is_valid_pos (xy : nat * nat) := 
  ((Nat.leb (fst xy) 7) && (Nat.leb (snd xy) 7))%bool.

Definition is_upper_left (xy : nat * nat) :=
  ((Nat.leb (fst xy) 3) && (Nat.leb (snd xy) 3))%bool.

Definition is_upper_right (xy : nat * nat) :=
  (negb (Nat.leb (fst xy) 3) && (Nat.leb (snd xy) 3))%bool.

Definition is_lower_left (xy : nat * nat) :=
  ((Nat.leb (fst xy) 3) && negb (Nat.leb (snd xy) 3))%bool.

Definition is_lower_right (xy : nat * nat) :=
  (negb (Nat.leb (fst xy) 3) && negb (Nat.leb (snd xy) 3))%bool.

Definition rotatepos_90 (xy : nat * nat) := 
  (snd xy, (7 - fst xy)%nat).

Definition rotatepos_180 (xy : nat * nat) := 
  rotatepos_90 (rotatepos_90 xy).

Definition rotatepos_270 (xy : nat * nat) := 
  rotatepos_90 (rotatepos_180 xy).

Lemma rotatepos_360 xy :
  is_valid_pos xy = true -> rotatepos_90 (rotatepos_270 xy) = xy.
Proof.
destruct xy as [x y];
  do 8 (try destruct x as [|x]);
  do 8 (try destruct y as [|y]); simpl; auto; try discriminate.
Qed.

Lemma rotatepos_upper_right xy :
  is_valid_pos xy = true ->
  is_upper_right xy = true -> is_upper_left (rotatepos_90 xy) = true.
Proof.
destruct xy as [x y];
  do 8 (try destruct x as [|x]);
  do 8 (try destruct y as [|y]); simpl; auto; try discriminate.
Qed.

Lemma rotatepos_lower_right xy :
  is_valid_pos xy = true ->
  is_lower_right xy = true -> is_upper_left (rotatepos_180 xy) = true.
Proof.
destruct xy as [x y];
  do 8 (try destruct x as [|x]);
  do 8 (try destruct y as [|y]); simpl; auto; try discriminate.
Qed.

Lemma rotatepos_lower_left xy :
  is_valid_pos xy = true ->
  is_lower_left xy = true -> is_upper_left (rotatepos_270 xy) = true.
Proof.
destruct xy as [x y];
  do 8 (try destruct x as [|x]);
  do 8 (try destruct y as [|y]); simpl; auto; try discriminate.
Qed.

(* direction  0 = Up 1 = Left  2 = Down 3 Rught *)

Definition is_valid_dir (d : nat) := (Nat.leb d 3).

Definition rotatedir_90 d := Nat.modulo (4 + d - 1) 4.

Definition rotatedir_180 (d : nat) := 
  rotatedir_90 (rotatedir_90 d).

Definition rotatedir_270 (d : nat) := 
  rotatedir_90 (rotatedir_180 d).

Lemma rotatedir_360 d :
  is_valid_dir d = true -> rotatedir_90 (rotatedir_270 d) = d.
Proof.
do 4 (try destruct d as [|d]); simpl; auto; try discriminate.
Qed.

Fixpoint lb_to_int (l : list bool) := 
match l with
| true :: l1 => (1 + 2 * (lb_to_int l1))%uint63
| false :: l1 => (2 * (lb_to_int l1))%uint63
| [] => 0%uint63
end.

Definition mk_state npos nbin := 
  let v := lb_to_int (bin_decode 22 6 nbin) in 
  let cube := (v >> 16)%uint63 in
  let board := (v land (1 << 16 - 1))%uint63 in 
  ((cube << 4 + npos) << 16 + board)%uint63.


From puzzle Require Import cube.
Require Import String.

(* Empty board position (0, 0) *)
Compute print_state (mk_state 0 0).
(* Empty board position (3, 3) *)
Compute print_state (mk_state 15 0).
Compute bin_compute 22 6.
(* Full board position (0, 0) *)
Compute print_state (mk_state 0 2).

(* Function that takes a state and return a direction *)
Definition get_direction (state : int) : int := 3%uint63.

(* From upper left to full position *)
Definition ul_to_full (p : int) :=
  if (p =? 2)%uint63 then 4%uint63 else
  if (p =? 3)%uint63 then 5%uint63 else p.

Compute array_find big_array' 252.

(* Function that get the direction from a state *)
Definition get_dir (s : int) := 
  match array_find big_array' s with
  | Some x => x - 1
  | _ => 0
  end. 

From Bignums Require Import BigN.
Require Import ZArith.

Definition bigN_of_int (z : int) := (BigN.N_of_Z (to_Z z)).

Definition add_state npos nbin (res : bigN) := 
  let nbit := ((npos + nbin << 2) << 1)%uint63 in
  let state := mk_state (ul_to_full npos) nbin in 
  let dir := get_dir state in 
  (BigN.lor res (BigN.shiftl (bigN_of_int dir) (bigN_of_int nbit)))%bigN.

Definition add_all_pos_state nbin res := 
let res1 := add_state 0 nbin res in
let res2 := add_state 1 nbin res1 in
let res3 := add_state 2 nbin res2 in
let res4 := add_state 3 nbin res3 in res4.

Fixpoint iter_add_state n nbin res := 
  let res1 := add_all_pos_state nbin res in 
  match n with 0 => res1 | S n1 => iter_add_state n1 (nbin + 1) res1 end.

Compute bin_compute 22 6.
(* 74613 *)
Time Definition mk_big_number := Eval vm_compute in iter_add_state 74612 0 0.

Definition bigN_to_int (z : bigN) := (of_Z (BigN.to_Z z)).

Definition get_dir_from_number npos nbin (num : bigN) := 
  let nbit := ((npos + nbin << 2) << 1)%uint63 in
  bigN_to_int (BigN.land (BigN.shiftr num (bigN_of_int nbit)) 3).

Compute get_dir_from_number 0 0 mk_big_number.

