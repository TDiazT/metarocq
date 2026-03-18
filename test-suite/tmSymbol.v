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
   Undeclared quality: s. *)

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

(* Monomorphic identity-like symbol *)
MetaRocq Run (tmSymbolU "id_sym" Datatypes.false
  (poly_ctx_no_constraints (mk_bound_names [] [nNamed "u"]))
  (tProd (mkBindAnn (nNamed "A") Relevant)
    <% Set %>
    (tProd (mkBindAnn nAnon Relevant) (tRel 0) (tRel 1)))).

About id_sym.

(* ------------------------------------------------------------------ *)
(* Tests for quality variables, RelevanceVar, and global sort quoting  *)
(* ------------------------------------------------------------------ *)

(* Test: polymorphic symbol using a global sort (Exc).
   Exercises quote_qvar with QVar.Global and quote_quality with qVar. *)
#[universes(polymorphic)] Symbol (raise_test@{u} : forall (A : Type@{Exc;u}), A).
MetaRocq Run (tmQuote raise_test >>= tmPrint).
About raise_test.

Set Universe Polymorphism.

(* Test: symbol with Exc quality in an instance.
   Exercises denoting Quality.qVar with QVar.Global. *)
Definition exc_qvar_test : QVar.t :=
  QVar.Global {| QGlobal.library := ["tmSymbol"]; QGlobal.id := "Exc" |}.

MetaRocq Run (tmSymbolU "exc_inst_test" false
  (poly_ctx_no_constraints (mk_bound_names [] [nNamed "u"]))
  (tProd (mkBindAnn (nNamed "x") Relevant)
    (tSort (sQVar exc_qvar_test (Universe.make' (Level.lvar 0))))
    (tRel 0))).
About exc_inst_test.
