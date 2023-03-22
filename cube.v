Require Import List Uint63 String.
Import ListNotations.

Open Scope uint63_scope.

(* The number of bits for the board *)
Definition size_board := 4.
Definition nsize_board := 4%nat.
Definition size_board2 := size_board * size_board.
Definition nsize_board2 := (nsize_board * nsize_board)%nat.

(* The number of bits for the position *)
Definition size_position := 4.
Definition nsize_position := 4%nat.

Definition size_board2_position := size_board2 + size_position.

(* Tne number of bits for the cube *)
Definition size_cube := 6.
Definition size_all := size_cube + size_board2_position.

Definition mask_all := (1 << size_all) -1.

Definition mask_board := (1 << size_board2) -1.
Definition clean_board := mask_all lxor mask_board.
Definition get_board s := (s land mask_board).
Definition set_board s i := (s land clean_board) lor i.

Fixpoint mk_string n s :=
  match n with 0 => ""%string | S n1 => append s (mk_string n1 s) end.

Fixpoint print_line s n :=
  match n with 
  | 0 => ""%string  
  | S n1 => if (is_zero (s land 1)) then
              append " "%string (print_line (s >> 1) n1) 
            else
              append "X"%string (print_line (s >> 1) n1) 
    end.

Definition string_return := "
"%string.

Fixpoint print_board_rec s n :=
  match n with 
  | 0 => ""%string  
  | S n1 => append "|"%string
             (append (append (print_line s nsize_board) "|"%string)
                     (append string_return
                        (print_board_rec (s >> size_board) n1)))
    end.

Definition print_board b := 
  append string_return (print_board_rec b nsize_board).

(* Test *)
Compute (print_board 34).
Compute (print_board (get_board (set_board mask_all 34))).

Definition mask_position := (((1 << size_position) - 1) << size_board2).
Definition clean_position := mask_all lxor mask_position.
Definition get_position s := (s land mask_position) >> size_board2.
Definition get_positionX s :=
  (get_position s) land ((1 << (size_position / 2)) - 1).
Definition get_positionY s := (get_position s) >> (size_position / 2).
Definition set_position s i := (s land clean_position) lor (i << size_board2).
Definition set_positionXY s x y := 
  set_position s ((y << (size_position / 2)) lor x).

(* Lazyness : only till 9  *)
Definition print_one_position p :=
 if p =? 0 then "0"%string else
 if p =? 1 then "1"%string else
 if p =? 2 then "2"%string else
 if p =? 3 then "3"%string else
 if p =? 4 then "4"%string else
 if p =? 5 then "5"%string else
 if p =? 6 then "6"%string else
 if p =? 7 then "7"%string else
 if p =? 8 then "8"%string else
 if p =? 9 then "9"%string else "?"%string.

Definition print_position p :=
  append (print_one_position (p land ((1 << (size_position / 2)) - 1)))
  (append ", " (print_one_position (p >> (size_position / 2)))).

(* Test *)
Compute let s := set_positionXY mask_all 2 1 in
      (print_position (get_position s)).
Definition mask_cube := (((1 << size_cube) - 1) << size_board2_position).
Definition clean_cube := mask_all lxor mask_cube.
Definition get_cube s := (s land mask_cube) >> size_board2_position.
Definition set_cube s i := (s land clean_cube) lor (i << size_board2_position).

(* Test *)
Compute get_cube (set_cube mask_all 12).


(* Cube
       ---
       |4|
     -------
     |2|1|5|
     -------
       |3|
       ---
       |6|
       ---       
*)



Definition d1 := 1 << 5.
Definition get_d1 c := (c >> 5) land 1.
Definition d2 := 1 << 4.
Definition get_d2 c := (c >> 4) land 1.
Definition d3 := 1 << 3.
Definition get_d3 c := (c >> 3) land 1.
Definition d4 := 1 << 2.
Definition get_d4 c := (c >> 2) land 1.
Definition d5 := 1 << 1.
Definition get_d5 c := (c >> 1) land 1.
Definition d6 := 1.
Definition get_d6 c := c land 1.
Definition mk_cube v1 v2 v3 v4 v5 v6 :=
  (((((((v1 << 1 lor v2) << 1) lor v3) << 1) lor v4) << 1) lor v5) << 1 lor v6.

Definition print_cube c :=
  let f x := if is_zero x then "O"%string else "X"%string in
  let res1 := append "         "%string 
                (append (f (get_d4 c)) string_return) in 
  let res2 := append "        "%string 
                (append 
                  (append (f (get_d2 c))(append (f (get_d1 c)) (f (get_d5 c))))
                   string_return) in
   let res3 := append "         "%string 
                (append (f (get_d3 c)) string_return) in 
   let res4 := append "         "%string 
                (append (f (get_d6 c)) string_return) in 
   let res5 := string_return in 
   append (append (append (append (append
      string_return res1) res2) res3) res4) res5. 

Compute print_cube (mask_cube >> size_board2_position).

(* Test *)
Compute let c := mk_cube 0 1 0 1 0 1 in
  (get_d1 c, get_d2 c, get_d3 c, get_d4 c, get_d5 c, get_d6 c). 

(* Rol Up 
       ---
       |6|
     -------
     |2|4|5|
     -------
       |1|
       ---
       |3|
       ---       

*)

Definition roll_up c :=
  mk_cube (get_d4 c) (get_d2 c) (get_d1 c) (get_d6 c) (get_d5 c) (get_d3 c).

(* Down
       ---
       |1|
     -------
     |2|3|5|
     -------
       |6|
       ---
       |4|
       ---       
*)

Definition roll_down c :=
  mk_cube (get_d3 c) (get_d2 c) (get_d6 c) (get_d1 c) (get_d5 c) (get_d4 c).

(* Test *)
Compute print_cube 13.
Compute print_cube (roll_down 13).
Compute print_cube (roll_up (roll_down 13)).
Compute print_cube (roll_up (roll_up (roll_up (roll_up 13)))).

(* Right
       ---
       |4|
     -------
     |1|5|6|
     -------
       |3|
       ---
       |2|
       ---       
*)

Definition roll_right c :=
  mk_cube (get_d5 c) (get_d1 c) (get_d3 c) (get_d4 c) (get_d6 c) (get_d2 c).

(* Left
       ---
       |4|
     -------
     |6|2|1|
     -------
       |3|
       ---
       |5|
       ---       
*)

Definition roll_left c :=
  mk_cube (get_d2 c) (get_d6 c) (get_d3 c) (get_d4 c) (get_d1 c) (get_d5 c).


(* Test *)
Compute print_cube 13.
Compute print_cube (roll_left 13).
Compute print_cube (roll_left (roll_right 13)).
Compute print_cube (roll_right (roll_right (roll_right (roll_right 13)))).

Fixpoint in_state s1 l := 
  match l with 
  | nil => false 
  | s2 :: l1 => if s2 <=? s1 then (s1 =? s2) else in_state s1 l1
  end.

Fixpoint add_state s1 l := 
  match l with 
  | nil => s1 :: nil 
  | s2 :: l1 => if s2 <=? s1 then 
                  if (s1 =? s2) then l else s1 :: l1 
                  else s2 :: add_state s1 l1
  end.

Compute (add_state 11 (add_state 10 (add_state 11 nil))).

Definition swap_state s := 
  let c := get_cube s in
  let b := get_board s in 
  let p := get_position s in 
  let d1 := get_d1 c in 
  let v := (b >> p) land 1 in 
  let s1 := set_cube s
    (mk_cube v (get_d2 c) (get_d3 c) (get_d4 c) (get_d5 c) (get_d6 c)) in 
  let b1 := if (v =? d1) then b else
              if is_zero v then b lor (1 << p) else b lxor (1 << p) in
  set_board s1 b1.

Definition s0 := set_cube (set_positionXY 0 1 2) ((1 << size_cube) - 1).

Compute print_cube (get_cube (swap_state s0)).
Compute print_board (get_board (swap_state s0)).

Definition one_step s vls := 
  let px := get_positionX s in 
  let py := get_positionY s in
  let c := get_cube s in 
  let (r1,vls1) := if is_zero px then (nil, vls) else
      let c1 := roll_left c in 
      let s1 := swap_state (set_cube (set_positionXY s (px - 1) py) c1) in
      if in_state s1 vls then (nil, vls) else
      (s1 :: nil, add_state s1 vls) in
  let (r2,vls2) := if px =? (size_board - 1) then (r1, vls1) else
      let c1 := roll_right c in 
      let s1 := swap_state (set_cube (set_positionXY s (px + 1) py) c1) in
      if in_state s1 vls1 then (r1, vls1) else
      (s1 :: r1, add_state s1 vls1) in
  let (r3,vls3) := if is_zero py then (r2, vls2) else
      let c1 := roll_up c in 
      let s1 := swap_state (set_cube (set_positionXY s px (py - 1)) c1) in
      if in_state s1 vls2 then (r2, vls2) else
      (s1 :: r2, add_state s1 vls2) in
  let (r4,vls4) := if py =? (size_board - 1) then (r3, vls3) else
      let c1 := roll_down c in 
      let s1 := swap_state (set_cube (set_positionXY s px (py + 1)) c1) in
      if in_state s1 vls3 then (r3, vls3) else
      (s1 :: r3, add_state s1 vls3) in
  (r4, vls4).

Definition print_state s := 
    append (print_cube (get_cube s)) 
    (append (print_position (get_position s)) (print_board (get_board s))).

Compute print_state 19.
Compute map print_state (fst (one_step 19 nil)).

Fixpoint first_vls (f : int -> list int -> bool) ls vls := 
  match ls with 
  | nil => false
  | s1 :: ls1 => 
   if f s1 vls then true else first_vls f ls1 vls
  end.

Fixpoint solve n s vls := 
  if get_cube s =? ((1 << size_cube) - 1) then true else
  match n with  
  | 0 => false
  | S n1 => let '(ls1, vls1) := one_step s vls in 
            first_vls (solve n1) ls1 vls1
  end.


Fixpoint gen_all n p m k s :=
  match n with 
  | 0 => true 
  | S n1 => if is_zero ((s >> p) land 1) then
            let s1 := s lor (1 << p) in 
            match m with 
            | 0 => let s2 := swap_state s1 in
                   if solve k s2 (s2 :: nil) then gen_all n1 (p + 1) m k s   
                   else false     
            | S m1 => if gen_all n1 (p + 1) m1 k s1 
                      then gen_all n1 (p + 1) m k s
                      else false
            end else gen_all n1 (p + 1) m k s
   end.

Compute print_state 252.
Compute get_board 252.
Compute print_board 31.

Time Compute gen_all 15%nat 0 0%nat 16 31.
(* 2.5 s *)
(*
Time Compute gen_all 15%nat 0 1%nat 16 15.
(* 22 s *)
Time Compute gen_all 15%nat 0 2%nat 16 7.
(* 63 s *)
Time Compute gen_all 15%nat 0 3%nat 16 3.
(* 280 s *)
Time Compute gen_all 15%nat 0 4%nat 16 1.
(* 591 s *)
Time Compute gen_all 15%nat 0 5%nat 21 0.
(* 2939 s *)
Time Compute gen_all 15%nat 0 5%nat 21 (set_positionXY 0 0 1).
(* 3594s *)
*)