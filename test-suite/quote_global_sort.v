From MetaRocq.Utils Require Import utils.
From MetaRocq.Template Require Import All.
Import MRMonadNotation.

Set Universe Polymorphism.
#[universes(polymorphic=no)]
Sort Exc.

MetaRocq Run (tmQuote Type@{Exc;Set} >>= tmPrint).

Axiom ax_raise@{u} : forall (A : Type@{Exc;u}), A.

MetaRocq Run (tmQuote ax_raise >>= tmPrint).

(* This one requires -allow-rewrite-rules enabled
Symbol raise@{u} : forall (A : Type@{Exc;u}), A.

MetaRocq Run (tmQuote raise >>= tmPrint).
*)
