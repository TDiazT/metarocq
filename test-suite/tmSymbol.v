From MetaRocq.Utils Require Import utils.
From MetaRocq.Template Require Import All.
From Stdlib Require Import List.
Import ListNotations.
Import MRMonadNotation.

Definition empty_poly_ctx := 
  let ctx := AUContext.make empty_bound_names ConstraintSet.empty in
Polymorphic_ctx ctx.

MetaRocq Run (tmSymbolU "foo" false empty_poly_ctx <% Set %>).

MetaRocq Run (tmQuote Type >>= tmPrint).

Sort Exc.

MetaRocq Run (tmQuote Type@{Exc;0} >>= tmPrint).

MetaRocq Run (tmQuote Type@{Exc;0} >>= tmSymbolU "exc_ty" false empty_poly_ctx).

About exc_ty. 

Definition poly_ctx_no_constraints (bnames : bound_names) : universes_decl :=
  let ctx := AUContext.make bnames ConstraintSet.empty in
Polymorphic_ctx ctx.

Definition quoted_type (sort_i lvl_i : nat) := tSort (sQVar (QVar.var sort_i) (Universe.make' (Level.lvar  lvl_i))).  

Fail MetaRocq Run (tmSymbolU "bar" false (poly_ctx_no_constraints (mk_bound_names [nNamed "s"] [])) <% Type@{s;0} %>).
(* The command has indeed failed with message:
(* Undeclared quality: s.*)
MetaRocq Run (tmSymbolU "bar" false (poly_ctx_no_constraints (mk_bound_names [nNamed "s"] [nNamed "u"])) (quoted_type 0 0)). *)

About bar.

MetaRocq Run (
  s1 <- tmFreshName "s1";;
  s2 <- tmFreshName "s2";;
  u1 <- tmFreshName "u1";;
  u2 <- tmFreshName "u2";;
  let sorts := [nNamed s1; nNamed s2] in
  let lvls := [nNamed u1; nNamed u2] in
  let bound_n := mk_bound_names sorts lvls in 
  let ty :=
  tProd (mkBindAnn nAnon Relevant)
      (quoted_type 0 0) 
      (quoted_type 1 1) 
      in 
tmSymbolU "zed" false (poly_ctx_no_constraints bound_n) ty).

About zed.

Check zed@{Type Prop; Set Set}.

MetaRocq Run (tmSymbolU "id_sym" Datatypes.false
  (poly_ctx_no_constraints (mk_bound_names [] [nNamed "u"]))
  (tProd (mkBindAnn (nNamed "A") Relevant)
    (tSort (Sort.type0))
    (tProd (mkBindAnn nAnon Relevant) (tRel 0) (tRel 1)))).
