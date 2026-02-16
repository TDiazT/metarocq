From MetaRocq.Utils Require Import utils.
From MetaRocq.Template Require Import All.
From Stdlib Require Import List.
Import ListNotations.
Import MRMonadNotation.


(* Rewrite Rule pplus_rewrite :=
| ?n ++ 0 => ?n
| ?n ++ S ?m => S (?n ++ ?m)
| 0 ++ ?n => ?n
| S ?n ++ ?m => S (?n ++ ?m). *)

MetaRocq Run (
  tmSymbol "f_rr" (nat -> nat -> nat) ;;
  tmRewriteRule "pplus_n_0_rewrite_tm"
    [ ("f_rr ?n 0", "?n") ]).

About f_rr.    
Infix "++" := f_rr.

Eval cbn in 1 ++ 0.
(* Doesn't reduce *)
Eval cbn in 0 ++ 1.

MetaRocq Run (tmRewriteRule "pplus_rewrite"
    [ ("?n ++ S ?m", "S (?n ++ ?m)");
      ("S ?n ++ ?m", "S (?n ++ ?m)"); 
      ("0 ++ ?n", "?n") ]).
      
Eval cbn in 0 ++ 1.    
Eval cbn in 1 ++ 3.   
Eval cbn in 3 ++ 1.

Set Universe Polymorphism.
#[universes(polymorphic=no)]
Sort Exc.

#[unfold_fix]
Symbol (raise : forall (A : Type@{Exc; Set}), A).

Inductive nat : Type@{Exc; Set} :=
 | O : nat 
 | S : nat -> nat.

Inductive bool : Type@{Exc; Set} :=
 | true
 | false.
 
Rewrite Rule raise_nat_match :=
| match raise nat as t0 return ?P with 
  | O => _
  | _ => _ 
  end => raise (?P@{t0 := raise nat}).
  
Eval cbn in match raise nat with | O => O | S n => S n end.
Eval cbn in match raise nat with | O => true | S n => false end.

Eval cbn in match raise bool with | true => O | false => S O end.
  
MetaRocq Run (tmRewriteRule "raise_bool_match"
    [ ("match raise bool as t0 return ?P with | true => _ | _ => _ end", "raise (?P@{t0 := raise bool})")]).
    
Eval cbn in match raise bool with | true => O | false => S O end.
    

  

