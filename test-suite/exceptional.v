From MetaRocq.Utils Require Import utils.
From MetaRocq.Template Require Import All.
From Stdlib Require Import List.
Import ListNotations.
Import MRMonadNotation.

Set Universe Polymorphism.

Definition nAnonRel (rel : relevance) : aname :=
  {| binder_name := nAnon; binder_relevance := rel |}.

#[universes(polymorphic=no)]
Sort Exc.

#[unfold_fix]
Symbol (raise@{u} : forall (A : Type@{Exc;u}), A).

MetaRocq Quote Definition tmRaise := raise.

Print tmRaise.

Definition tmAsIndRef (ty : term) : TemplateMonad (term * inductive * Instance.t) :=
  match ty with
  | tInd ind u => ret (ty, ind, u)
  | _ => tmPrint ty ;; tmFail "not an inductive type"
  end.

Definition join_args (xs : list string) : string :=
  List.fold_left (fun acc x => acc ^ " " ^ x) xs "".

Definition ctor_pat_with_metas (cname : ident) (arity : nat) : string :=
  let args := List.map (fun n => "?x" ^ string_of_nat n) (seq 0 arity) in
  if Nat.eqb arity 0
  then cname
  else "(" ^ cname ^ join_args args ^ ")".

Definition ctor_pat_for_match (cname : ident) (arity : nat) : string :=
  let args := List.map (fun _ => "_") (seq 0 arity) in
  if Nat.eqb arity 0
  then cname
  else cname ^ join_args args.

Definition raise_rule_lhs (ind_name first_ctor : ident) (first_arity : nat) : string :=
  "match raise ?A as t0 return ?P with | "
  ^ ctor_pat_for_match first_ctor first_arity ^ " => _ | _ => _ end".

Definition raise_rule_rhs (ind_name : ident) : string :=
  "raise (?P@{t0 := raise ?A})".

Definition get_ind_and_body_from_ind (ind : inductive)
  : TemplateMonad (kername * one_inductive_body) :=
  let kn := inductive_mind ind in
  decl <- tmQuoteInductive kn ;;
  match nth_error decl.(ind_bodies) ind.(inductive_ind) with
  | None => tmFail "cannot find one_inductive_body for this inductive"
  | Some body =>
      if Nat.eqb decl.(ind_npars) 0 then
        if Nat.eqb (List.length body.(ind_indices)) 0 then
          ret (kn, body)
        else tmFail "indexed inductives are not supported yet"
      else tmFail "parametric inductives are not supported yet"
  end.

Definition tmLocateIndRef (q : qualid) : TemplateMonad inductive :=
  gr <- tmLocate1 q ;;
  match gr with
  | IndRef ind => ret ind
  | _ => tmFail "not an inductive"
  end.

Definition get_rect_type (ind_name : ident) : TemplateMonad term :=
  gr <- tmLocate1 (ind_name ^ "_rect") ;;
  match gr with
  | ConstRef kn =>
      cb <- tmQuoteConstant kn false ;;
      ret cb.(cst_type)
  | _ => tmFail "_rect is not a constant"
  end.

Definition common_kn (s : ident) : kername :=
  (MPfile ["Common"; "TemplateMonad"; "Template"; "MetaRocq"], s).

Definition tmMkSymbol_from_term (id : qualid) (ty : term) : TemplateMonad unit :=
  tmBind (tmUnquote ty) (fun t' =>
  tmBind (tmEval (unfold (common_kn "my_projT1")) (my_projT1 t')) (fun ty' =>
  tmSymbol id ty')).

Fixpoint insert_raise_before_last_prod (elim_ty : term) : TemplateMonad term :=
  match elim_ty with
  | tProd b dom codom =>
      match codom with
      | tProd _ _ _ =>
          codom' <- insert_raise_before_last_prod codom ;;
          ret (tProd b dom codom')
      | _ =>
          let raise_ind := mkApp tmRaise dom in
          let raise_case_ty := subst10 raise_ind codom in
          let lifted_codom := lift0 1 codom in
          ret (tProd (nAnonRel Relevant) raise_case_ty (tProd b dom lifted_codom))
      end
  | _ => tmFail "expected a product type"
  end.

Definition gen_raise_rule (q : qualid) : TemplateMonad unit :=
  ind <- tmLocateIndRef q ;;
  '(kn, body) <- get_ind_and_body_from_ind ind ;;
  let '(_, ind_name) := kn in
  match body.(ind_ctors) with
  | [] => tmFail "empty constructor list"
  | c :: _ =>
      let lhs := raise_rule_lhs ind_name c.(cstr_name) c.(cstr_arity) in
      let rhs := raise_rule_rhs ind_name in
      tmRewriteRule ("raise_" ^ ind_name ^ "_rr") [(lhs, rhs)]
  end.

Definition gen_catch_symbol_and_rules (q : qualid) : TemplateMonad unit :=
  ind <- tmLocateIndRef q ;;
  '(kn, body) <- get_ind_and_body_from_ind ind ;;
  let '(_, ind_name) := kn in
  let catch_name := ind_name ^ "_catchT" in
  let rect_name := ind_name ^ "_rect" in

  rect_ty <- get_rect_type ind_name ;;
  catch_ty <- insert_raise_before_last_prod rect_ty ;;
  tmMkSymbol_from_term catch_name catch_ty ;;

  let ctors := body.(ind_ctors) in
  let handlers := List.map (fun c => "?H" ^ c.(cstr_name)) ctors in
  let ctor_rules :=
    List.map (fun c =>
      let cpat := ctor_pat_with_metas c.(cstr_name) c.(cstr_arity) in
      let lhs := catch_name ^ " ?P" ^ join_args handlers ^ " ?Hraise " ^ cpat in
      let rhs := rect_name ^ " ?P" ^ join_args handlers ^ " " ^ cpat in
      (lhs, rhs)) ctors
  in
  let raise_rule :=
    (catch_name ^ " ?P" ^ join_args handlers ^ " ?Hraise (raise ?A)",
     "?Hraise")
  in
  tmRewriteRule ("catch_" ^ ind_name ^ "_rr") (ctor_rules ++ [raise_rule]).

Definition gen_exceptional (q : qualid) : TemplateMonad unit :=
  gen_raise_rule q ;;
  gen_catch_symbol_and_rules q.

Definition gen_exceptional_quoted (dom : term) : TemplateMonad unit :=
  '(_, ind, _) <- tmAsIndRef dom ;;
  let kn := inductive_mind ind in
  let '(_, ind_name) := kn in
  gen_exceptional ind_name.
  
Inductive bool@{s;u} : Type@{s;u} := true | false.
MetaRocq Run (gen_exceptional "bool").

Inductive nat@{s;u} : Type@{s;u} :=
| O : nat 
| S : nat -> nat.

MetaRocq Run (gen_exceptional "nat").  (* no quotation of the inductive term *)

About bool_catchT.
About nat_catchT.
