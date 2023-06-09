(** * An Evaluation Function for Imp *)


(** Taken from the chapter Imp:
  https://softwarefoundations.cis.upenn.edu/lf-current/ImpCEvalFun.html

    It might be a good idea to read the chapter before or as you
    develop your solution.
*)

From Coq Require Import Lia.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.PeanoNat.
Import Nat.
From Coq Require Import Arith.EqNat.
From FirstProject Require Import Imp Maps.

(* Let's import the result datatype from the relational evaluation file *)
From FirstProject Require Import RelationalEvaluation.

(** We can improve the readability of this version by introducing a
    bit of auxiliary notation to hide the plumbing involved in
    repeatedly matching against optional states. *)

Notation "'LETOPT' x <== e1 'IN' e2"
   := (match e1 with
         | Some x => e2
         | None => None
       end)
   (right associativity, at level 60).

(** 2.1. DONE: Implement ceval_step as specified. To improve readability,
               you are strongly encouraged to define auxiliary notation.
               See the notation LETOPT commented above (or in the ImpCEval chapter).
*)

Fixpoint ceval_step (st : state) (c : com) (i : nat): option (state*result) :=
  match i with
  | O => None
  | S i' => match c with
            (* Break *)
            | <{ break }> => Some (st, SBreak)
            
            (* Skip *)
            | <{ skip }> => Some (st, SContinue)
            
            (* Assign *)
            | <{ x := a1 }> => Some (x !-> (aeval st a1) ; st, SContinue)

            (* Seq *)
            | <{ c1 ; c2 }> => LETOPT x <== ceval_step st c1 i' IN
                               match x with
                               | (st', SBreak) => Some (st', SBreak)
                               | (st', SContinue) => ceval_step st' c2 i'
                               end
            (* If *)
            | <{ if b then c1 else c2 end }> => match beval st b with
                                                | true => ceval_step st c1 i'
                                                | false => ceval_step st c2 i'
                                                end
            (* While *)
            | <{ while b do c end }> => match beval st b with
                                        | false => Some (st, SContinue)
                                        | true => LETOPT x <== ceval_step st c i' IN
                                                  match x with
                                                  | (st', SBreak) => Some (st', SContinue)
                                                  | (st', SContinue) => ceval_step st' <{ while b do c end }> i'
                                                  end
                                        end
            end
end.

(* The following definition is taken from the book and it can be used to
   test the step-indexed interpreter. *)
Definition test_ceval (st:state) (c:com) :=
  match ceval_step st c 500 with
  | None    => None
  | Some (st, _) => Some (st X, st Y, st Z)
  end.

Example example_test_ceval :
     test_ceval empty_st

     <{ X := 2;
        if (X <= 1)
        then Y := 3
        else Z := 4
        end }>

     = Some (2, 0, 4).
Proof. reflexivity. Qed.

Example example_test_ceval2 :
     test_ceval empty_st

     <{ while true do
          skip
        end }>

     = None.
Proof. reflexivity. Qed.

(** 
  2.2. DONE: Prove the following three properties.
             Add a succint explanation in your own words of why `equivalence1` and `inequivalence1` are valid.
*)

(*
  Explanation: 
  This theorem states that there exists a point (i0) from which (i1 >= i0) evaluating the programs
  <{ break; c }> and <{ break; skip }> with i1 gas units produces the same output.
  This is true; in fact, it is true for all natural i1, so we can take i0 = 0. 
  It is true for i1 = 0 because both of them output None; furthermore, it is also true for i1 >=1 because both
  of them start with a break command, meaning that the state st will not be changed and the signal wil be SBreak.
*)
Theorem equivalence1: forall st c,
  exists i0, forall i1, i1>=i0 ->
  ceval_step st <{ break; c }> i1 = ceval_step st <{ break; skip }> i1.
Proof.
  intros. exists 0.
  intros. destruct i1 as [ | i1'].
  - simpl. reflexivity.
  - simpl. destruct i1'.
    * simpl. reflexivity.
    * simpl. reflexivity.  
Qed.

(*
  Explanation: 
  This theorem states that there exists a point (i0) from which (i1 >= i0) evaluating the programs
  <{ break; c }> and <{ skip }> with i1 gas units produces different outputs.
  This is true because, although both of them keep the state st, they produce different signals (SBreak and
  SContinue). However, this only happens for i1 >= 1, because for i1 = 0 they will both output None.
  Thus, we can take i0 = 1 and it will be true.
*)
Theorem inequivalence1: forall st c,
  exists i0, forall i1, i1>=i0 ->
  ceval_step st <{ break; c }> i1 <> ceval_step st <{ skip }> i1.
Proof.
  intros. exists 1.
  intros. destruct i1 as [ | i1'].
  - lia.
  - simpl. destruct i1'.
    * simpl. discriminate.
    * simpl. discriminate.
Qed.

(**
  Min. gas for the evaluator 
  terminating each program
*)
Compute ceval_step empty_st p1 6.
Compute ceval_step empty_st p2 5.

Theorem p1_equivalent_p2: forall st,
  exists i0, forall i1, i1>=i0 -> 
  ceval_step st p1 i1 = ceval_step st p2 i1.
Proof.
  intros. exists 6.
  intros. destruct i1.
  { lia. }
  { simpl. destruct i1.
    { lia. }
    { simpl. destruct i1.
      { lia. }
      { simpl. destruct i1.
        { lia. }
        { simpl. destruct i1.
          { lia. }
          { simpl. destruct i1.
            { lia. }
            { simpl. destruct i1.
              { reflexivity. }
              { reflexivity. }
            }
          }
        }
      }
    }
  }
Qed.
