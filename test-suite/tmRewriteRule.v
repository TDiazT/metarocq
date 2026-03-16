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
  tmSymbol "f_rr" false (nat -> nat -> nat) ;;
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
Unset Collapse Sorts ToType.
#[universes(polymorphic=no)]
Sort Exc.

#[unfold_fix]
Symbol (raise : forall (A : Type@{Exc; Set}), A).

Inductive nat : Type :=
 | O : nat
 | S : nat -> nat.

Inductive bool : Type :=
 | true
 | false.

Print name.
Locate name.
Set Debug "backtrace".
(* Test tmSymbolU with level polymorphism: declare a symbol forall (A : Type@{u}), A -> A *)
Fail MetaRocq Run (tmSymbolU "id_sym" Datatypes.false
  (Polymorphic_ctx (AUContext.make (mk_bound_names [] [nNamed "u"]) ConstraintSet.empty))
  (tProd (mkBindAnn (nNamed "A") Relevant)
    (tSort (sType (Universe.make' (Level.lvar 0))))
    (tProd (mkBindAnn nAnon Relevant) (tRel 0) (tRel 1)))).

(* Generate catch using the native Symbol command, which supports sort quality polymorphism *)
Symbol bool_catch@{s;u} : forall (P : bool -> Type@{s;u})
                            (Htrue : P true)
                            (Hfalse : P false)
                            (Hraise : P (raise bool))
                            (b : bool), P b.
Set Printing All.
Set Printing Universes.
Print bool_catch.

Eval cbn in (bool_catch (fun _ => True) I I I true).

Rewrite Rules bool_catch_red :=
  | bool_catch _ ?Htrue _ _ true => ?Htrue.

Eval cbn in (bool_catch (fun _ => True) I I I true).
Eval cbn in (bool_catch (fun _ => True) I I I false).
Eval cbn in (bool_catch (fun _ => True) I I I (raise bool)).

MetaRocq Run (tmRewriteRule "bool_catch_red_false"
  [("bool_catch _ _ ?Hfalse _ false", "?Hfalse");
  ("bool_catch _ _ _ ?Hraise (raise bool)", "?Hraise")

  ]

).

Eval cbn in (bool_catch (fun _ => True) I I I false).
Eval cbn in (bool_catch (fun _ => True) I I I (raise bool)).

Rewrite Rule raise_nat_match :=
| match raise nat as t0 return@{Exc;Set} ?P with
  | O => _
  | _ => _
  end => raise (?P@{t0 := raise nat}).

Eval cbn in match raise nat with | O => O | S n => S n end.
Eval cbn in match raise nat with | O => true@{Exc;} | S n => false end.

Eval cbn in match raise bool with | true => O@{Exc;} | false => S O end.

MetaRocq Run (tmRewriteRule "raise_bool_match"
    [ ("match raise bool as t0 return@{Exc;Set} ?P with | true => _ | _ => _ end", "raise (?P@{t0 := raise bool})")]).

Eval cbn in match raise bool with | true => O@{Exc;} | false => S O end.

