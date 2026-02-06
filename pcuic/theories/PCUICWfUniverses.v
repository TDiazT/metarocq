(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import Morphisms.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICCases PCUICInduction
     PCUICLiftSubst PCUICSigmaCalculus PCUICTyping PCUICWeakeningEnv PCUICWeakeningEnvTyp
     PCUICWeakeningConv PCUICWeakeningTyp
     PCUICSubstitution PCUICReduction PCUICCumulativity PCUICGeneration
     PCUICUnivSubst PCUICUnivSubstitutionConv.

From Equations Require Import Equations.
From Equations.Prop Require Import DepElim.
From Stdlib Require Import ssreflect ssrbool.

From MetaRocq.PCUIC Require Import PCUICInduction.

Lemma test_primu_mapu {term term'} pu pt fu (ft : term -> term') p :
  test_primu pu pt (mapu_prim fu ft p) =
  test_primu (pu ∘ fu) (pt ∘ ft) p.
Proof.
  destruct p as [? []] => //=. cbn.
  now rewrite forallb_map.
Qed.

Lemma test_primu_primProp {term} P pu (pt : term -> bool) pu' (pt' : term -> bool) p :
  tPrimProp P p ->
  (forall x, pu x = pu' x) ->
  (forall x, P x -> pt x = pt' x) ->
  test_primu pu pt p = test_primu pu' pt' p.
Proof.
  destruct p as [? []] => //=. cbn.
  intuition eauto. do 3 f_equal; eauto.
  solve_all.
Qed.

Section CheckerFlags.
  Context {cf:checker_flags}.

  Lemma subst_instance_id_mdecl Σ u mdecl :
    consistent_instance_ext Σ (ind_universes mdecl) u ->
    subst_instance u (abstract_instance (ind_universes mdecl)) = u.
  Proof using Type.
    intros cu.
    red in cu. red in cu.
    destruct (ind_universes mdecl) eqn:eqi.
    - destruct u; simpl in cu; try discriminate.
      unfold abstract_instance, subst_instance, subst_instance_instance.
      cbn. destruct cu. apply length_nil in H, H0. rewrite H H0 //.
    - simpl. destruct cst as [univs csts]. simpl.
      destruct u. unfold subst_instance, subst_instance_instance. cbn.
      unfold Instance.make. f_equal; rewrite map_mapi; simpl in *;
        destruct cu as [Hu [sizeu [sizeq vu]]]; now rewrite mapi_nth.
  Qed.

  Lemma declared_inductive_wf_ext_wk Σ mdecl mind :
    wf Σ ->
    declared_minductive Σ mind mdecl ->
    wf_ext_wk (Σ, ind_universes mdecl).
  Proof using Type.
    intros wfΣ decli. eapply declared_minductive_to_gen in decli.
    epose proof (weaken_lookup_on_global_env' _ _ (InductiveDecl mdecl) wfΣ decli); eauto.
    red. simpl. split; auto.
    Unshelve. all:eauto.
  Qed.

  Lemma declared_inductive_wf_global_ext Σ mdecl mind :
    wf Σ ->
    declared_minductive Σ mind mdecl ->
    wf_global_ext Σ (ind_universes mdecl).
  Proof using Type.
    intros wfΣ decli. eapply declared_minductive_to_gen in decli.
    split; auto.
    epose proof (weaken_lookup_on_global_env' _ _ (InductiveDecl mdecl) wfΣ decli); eauto.
    Unshelve. all:eauto.
  Qed.

  Lemma udecl_prop_in_var_poly {Σ : global_env_ext} {n} :
    LevelSet.In (Level.lvar n) (levels_of_udecl Σ.2) ->
    ∑ ctx, Σ.2 = Polymorphic_ctx ctx.
  Proof using Type. clear cf.
    intros lin.
    destruct (Σ.2); intuition eauto.
    simpl in lin. lsets.
  Qed.

  Lemma udecl_in_var_quality_poly {Σ : global_env_ext} {n} :
    QualitySet.In (Quality.var n) (qualities_of_udecl Σ.2) -> ∑ ctx, Σ.2 = Polymorphic_ctx ctx.
  Proof using Type. clear cf.
    intros lin. destruct (Σ.2); intuition eauto.
    simpl in lin. qsets.
  Qed.

  Hint Resolve declared_inductive_wf_ext_wk declared_inductive_wf_global_ext : pcuic.


  Lemma wf_sort_type0 Σ : wf_sort Σ Sort.type0.
  Proof using Type.
    simpl.
    intros l hin%LevelExprSet.singleton_spec.
    subst l. simpl.
    apply global_ext_levels_InSet.
  Qed.

  Lemma wf_sort_type1 Σ : wf_sort Σ Sort.type1.
  Proof using Type.
    simpl.
    intros l hin%LevelExprSet.singleton_spec.
    subst l. simpl.
    apply global_ext_levels_InSet.
  Qed.

  Lemma wf_universe_succ {Σ u} : wf_universe Σ u -> wf_universe Σ (Universe.succ u).
  Proof.
    intros h l hin.
    eapply Universes.spec_map_succ in hin as [x' [int ->]].
    simpl. now specialize (h _ int).
  Qed.

  Lemma wf_sort_super {Σ u} : wf_sort Σ u -> wf_sort Σ (Sort.super u).
  Proof using Type.
    destruct u; cbn => Hu.
    all: try apply wf_sort_type1.
    all: apply wf_universe_succ; auto.
    apply Hu.
  Qed.

  Lemma wf_universe_sup {Σ l l'} : wf_universe Σ l -> wf_universe Σ l' ->
    wf_universe Σ (Universe.sup l l').
  Proof using Type.
    intros Hu Hu' x [Hl|Hl]%LevelExprSet.union_spec.
    now apply (Hu _ Hl).
    now apply (Hu' _ Hl).
  Qed.

  Lemma wf_sort_sup {Σ l u} : wf_universe Σ l -> wf_sort Σ u ->
    wf_universe Σ (Sort.sup l u).
  Proof using Type.
    destruct u; cbn; auto using wf_universe_sup.
    intros ? []; by apply wf_universe_sup.
  Qed.

  Lemma wf_sort_product {Σ s s'} : wf_sort Σ s -> wf_sort Σ s' ->
    wf_sort Σ (Sort.sort_of_product s s').
  Proof using Type.
    destruct s' => //= Hu Hu'.
    - now apply wf_sort_sup.
    - destruct Hu'. split; tas.
      now apply wf_sort_sup.
  Qed.

  Hint Resolve wf_sort_type1 wf_sort_super wf_sort_product : pcuic.

  Definition wf_qvarb Σ qv :=
    QualitySet.mem (Quality.qVar qv) (global_ext_qualities Σ).

  Definition wf_qualityb Σ q :=
    QualitySet.mem q (global_ext_qualities Σ).

  Definition wf_quality Σ q :=
    QualitySet.In q (global_ext_qualities Σ).

  Definition wf_levelb Σ l :=
    LevelSet.mem l (global_ext_levels Σ).

  Definition wf_level Σ l :=
    LevelSet.In l (global_ext_levels Σ).

  Definition wf_instance Σ u :=
    Forall (wf_quality Σ) (Instance.qualities u) /\
      Forall (wf_level Σ) (Instance.universes u).

  Definition wf_instanceb Σ u :=
    forallb (wf_qualityb Σ) (Instance.qualities u) &&
      forallb (wf_levelb Σ) (Instance.universes u).

  Lemma wf_qualityP {Σ q} : reflect (wf_quality Σ q) (wf_qualityb Σ q).
  Proof using Type.
    unfold wf_quality, wf_qualityb.
    destruct QualitySet.mem eqn:e; constructor.
    now apply QualitySet.mem_spec in e.
    intros hin.
    now apply QualitySet.mem_spec in hin.
  Qed.

  Lemma wf_qvarP {Σ qv} : reflect (wf_qvar Σ qv) (wf_qvarb Σ qv).
  Proof using Type.
    apply wf_qualityP.
  Qed.

  Lemma wf_levelP {Σ l} : reflect (wf_level Σ l) (wf_levelb Σ l).
  Proof using Type.
    unfold wf_level, wf_levelb.
    destruct LevelSet.mem eqn:ls; constructor.
    now apply LevelSet.mem_spec in ls.
    intros hin.
    now apply LevelSet.mem_spec in hin.
  Qed.

  Lemma wf_instanceP {Σ u} : reflect (wf_instance Σ u) (wf_instanceb Σ u).
  Proof using Type.
    unfold wf_instance, wf_instanceb.
    apply andPP; apply forallbP => x.
    - apply wf_qualityP.
    - apply wf_levelP.
  Qed.

  Lemma wf_universe_subst_instance_univ (Σ : global_env_ext) univs ui u :
    wf Σ ->
    wf_universe Σ u ->
    wf_instance (Σ.1, univs) ui ->
    wf_universe (Σ.1, univs) (subst_instance ui u).
  Proof using Type.
    intros wfΣ Hl [_ Hu] e [[l n] [inl ->]]%In_subst_instance.
    destruct l as [|s|n']; simpl; auto.
    - apply global_ext_levels_InSet.
    - specialize (Hl (Level.level s, n) inl).
      simpl in Hl.
      apply monomorphic_level_in_global_ext in Hl.
      eapply LS.union_spec. now right.
    - specialize (Hl (Level.lvar n', n) inl).
      eapply LS.union_spec in Hl as [Hl|Hl].
      + unfold levels_of_udecl in Hl.
        destruct Σ.2.
        * simpl in Hu. simpl in *.
          unfold subst_instance; simpl.
          destruct nth_error eqn:hnth; simpl.
          eapply nth_error_forall in Hu; eauto.
          apply global_ext_levels_InSet.
        * unfold subst_instance. simpl.
          destruct (nth_error (Instance.universes ui) n') eqn:hnth.
          2:{ simpl. apply global_ext_levels_InSet. }
          eapply nth_error_forall in Hu. 2:eauto.
          simpl. apply Hu.
      + now apply not_var_global_levels in Hl.
  Qed.

  Lemma wf_quality_subst_instance_qvar (Σ : global_env_ext) univs ui qv :
    wf Σ ->
    wf_instance (Σ.1, univs) ui ->
    wf_quality (Σ.1, univs) (subst_instance_qvar ui qv).
  Proof using Type.
    intros wfΣ [Hq _].
    destruct qv; cbnr.
    rewrite nth_nth_error.
    destruct nth_error eqn:hnth.
    - eapply nth_error_forall in Hq; tea.
    - global_ext_qconst_InSet.
  Qed.

  Lemma wf_sort_subst_instance_sort (Σ : global_env_ext) univs u s :
    wf Σ ->
    wf_sort Σ s ->
    wf_instance (Σ.1, univs) u ->
    wf_sort (Σ.1, univs) (subst_instance u s).
  Proof using Type.
    destruct s; cbnr.
    - apply wf_universe_subst_instance_univ.
    - intros ? [] ?.
      eapply wf_quality_subst_instance_qvar with (qv := t) in H1 as Hq; tea.
      destruct subst_instance_qvar; cbnr.
      + now apply wf_universe_subst_instance_univ.
      + split; tas.
        now apply wf_universe_subst_instance_univ.
  Qed.

  Lemma wf_sort_instantiate Σ univs s u φ :
    wf Σ ->
    wf_sort (Σ, univs) s ->
    wf_instance (Σ, φ) u ->
    wf_sort (Σ, φ) (subst_instance_sort u s).
  Proof using Type.
    intros wfΣ Hs.
    apply (wf_sort_subst_instance_sort (Σ, univs) φ); auto.
  Qed.

  Lemma subst_instance_empty u :
    forallb (fun x => ~~ Level.is_var x) u ->
    subst_instance (Instance.make [] []) u = u.
  Proof using Type.
    induction u; simpl; intros Hu; auto.
    rewrite subst_instance_cons.
    move/andP: Hu => [] isv Hf.
    rewrite IHu //.
    now destruct a => /= //; auto.
  Qed.

  Lemma wf_quality_mono Σ q :
    wf Σ ->
    Forall (wf_quality (Σ, Monomorphic_ctx)) q ->
    forallb (fun x => ~~ Quality.is_var x) q.
  Proof using Type.
    intros wf.
    induction 1 => /= //.
    destruct x eqn:isv => /= //.
    apply QualitySet.union_spec in H as [H|H]; simpl in H.
    inversion H. apply QualitySet_triple_In in H; destruct H.
    inversion H. destruct H; inversion H.
  Qed.

  Lemma wf_level_mono Σ u :
    wf Σ ->
    on_udecl_prop Σ (Monomorphic_ctx) ->
    Forall (wf_level (Σ, Monomorphic_ctx)) u ->
    forallb (fun x => ~~ Level.is_var x) u.
  Proof using Type.
    intros wf uprop.
    induction 1 => /= //.
    destruct x eqn:isv => /= //.
    apply LS.union_spec in H as [H|H]; simpl in H.
    epose proof (@udecl_prop_in_var_poly (Σ, Monomorphic_ctx) _ H) as [ctx' eq].
    discriminate.
    now pose proof (not_var_global_levels wf _ H).
  Qed.

  Lemma wf_quality_sub Σ univs q :
    wf_quality (Σ, Monomorphic_ctx) q ->
    wf_quality (Σ, univs) q.
  Proof using cf.
    intros wfx.
    red in wfx |- *.
    eapply QualitySet.union_spec in wfx; simpl in *.
    destruct wfx as [wfx|wfx]. qsets.
    eapply QualitySet.union_spec. now right.
  Qed.

  Lemma wf_level_sub Σ univs u :
    wf_level (Σ, Monomorphic_ctx) u ->
    wf_level (Σ, univs) u.
  Proof using cf.
    intros wfx.
    red in wfx |- *.
    eapply LevelSet.union_spec in wfx; simpl in *.
    destruct wfx as [wfx|wfx]. lsets.
    eapply LevelSet.union_spec. now right.
  Qed.

  Lemma wf_instance_sub Σ univs u :
    wf_instance (Σ, Monomorphic_ctx) u ->
    wf_instance (Σ, univs) u.
  Proof using cf.
    intros [wfq wfu].
    split; eapply Forall_impl; eauto; intros x.
    - eapply wf_quality_sub.
    - eapply wf_level_sub.
  Qed.

  Lemma In_Level_global_ext_poly s Σ cst :
    LS.In (Level.level s) (global_ext_levels (Σ, Polymorphic_ctx cst)) ->
    LS.In (Level.level s) (global_levels Σ).
  Proof using Type.
    intros [hin|hin]%LS.union_spec.
    simpl in hin.
    now apply monomorphic_level_notin_AUContext in hin.
    apply hin.
  Qed.

  Lemma Forall_In (A : Type) (P : A -> Prop) (l : list A) :
    Forall P l -> (forall x : A, In x l -> P x).
  Proof using Type.
    induction 1; simpl; auto.
    intros x' [->|inx]; auto.
  Qed.

  Lemma wf_instance_In {Σ u} : wf_instance Σ u <->
    (forall l, In l (Instance.universes u) -> LS.In l (global_ext_levels Σ)) /\
      (forall q, In q (Instance.qualities u) -> QualitySet.In q (global_ext_qualities Σ)).
  Proof using Type.
    unfold wf_instance; split.
    - intros [wfq wfu]; split; intros ? H; eapply Forall_In in H; eauto; apply H.
    - intros [Hu Hq]; split; apply In_Forall; auto.
  Qed.

  Lemma univ_in_subst_instance l u u' :
    In l (Instance.universes (subst_instance u u')) ->
    In l (Instance.universes u) \/ In l (Instance.universes u') \/ l = Level.lzero.
  Proof using Type.
    destruct u' as [qs us]. induction us; simpl; auto.
    intros [].
    destruct a; simpl in *; subst; auto.
    destruct (nth_in_or_default n (Instance.universes u) Level.lzero); auto.
    specialize (IHus H). intuition auto.
  Qed.

  Lemma wf_quality_subst_instance Σ q u φ :
    wf Σ ->
    wf_instance (Σ, φ) u ->
    wf_quality (Σ, φ) (subst_instance u q).
  Proof using Type.
    intros wfΣ [Hq _]. destruct q; cbn; global_ext_qconst_InSet.
    destruct t. destruct φ.
    - red. unfold global_ext_qualities. cbn.
      rewrite QualitySet_union_empty nth_nth_error.
      destruct (nth_error (Instance.qualities u) n) eqn:e.
      * have Hin: In t (Instance.qualities u) by now eapply nth_error_In.
        eapply Forall_In in Hq; eauto.
      * now apply QualitySetProp.FM.add_1.
    - unfold wf_quality in Hq |- *. cbn. rewrite nth_nth_error.
      destruct (nth_error (Instance.qualities u) n) eqn:e; global_ext_qconst_InSet.
      eapply Forall_In in Hq; eauto. now eapply nth_error_In.
  Qed.

  Lemma wf_instance_subst_instance Σ univs u u' φ :
    wf Σ ->
    on_udecl_prop Σ univs ->
    wf_instance (Σ, univs) u' ->
    wf_instance (Σ, φ) u ->
    wf_instance (Σ, φ) (subst_instance u u').
  Proof using Type.
    intros wfΣ onup [Hq Hu] [cq cu].
    destruct univs.
    - unshelve epose proof (wf_quality_mono _ _ _ Hq); eauto.
      unshelve epose proof (wf_level_mono _ _ _ _ Hu); eauto.
      eapply forallb_Forall in H. split; apply Forall_map; solve_all; destruct x; simpl => //; red;
        global_ext_qconst_InSet.
      * apply global_ext_levels_InSet.
      * eapply wf_level_sub; eauto.
    - clear onup. split; eapply Forall_map, Forall_impl; eauto.
      * intros q _. apply wf_quality_subst_instance; auto.
        split; auto.
      * intros x wfx.
        red in wfx. destruct x => /= //.
        { red. apply global_ext_levels_InSet. }
        eapply In_Level_global_ext_poly in wfx.
        apply LS.union_spec; now right.
        eapply in_var_global_ext in wfx; simpl in wfx; auto.
        unfold AUContext.levels, AUContext.repr in wfx.
        destruct cst as [? cst]. cbn in wfx.
        eapply (proj1 (LevelSetProp.of_list_1 _ _)) in wfx.
        rewrite mapi_unfold in wfx.
        apply SetoidList.InA_alt in wfx as [? [<- wfx]]. simpl in wfx.
        eapply In_unfold_inj in wfx; [|congruence].
        destruct (nth_in_or_default n (Instance.universes u) (Level.lzero)).
        eapply Forall_In in cu; eauto. rewrite e.
        red. apply global_ext_levels_InSet.
  Qed.

  Section WfUniverses.
    Context (Σ : global_env_ext).

    Definition wf_universeb (u : Universe.t) : bool :=
      LevelExprSet.for_all (fun l => LevelSet.mem (LevelExpr.get_level l) (global_ext_levels Σ)) u.

    Lemma wf_universe_reflect {u : Universe.t} :
      reflect (wf_universe Σ u) (wf_universeb u).
    Proof using Type.
      eapply iff_reflect.
      rewrite LevelExprSet.for_all_spec.
      split; intros.
      - intros l Hl; specialize (H l Hl).
        now eapply LS.mem_spec.
      - intros l Hl. specialize (H l Hl).
        now eapply LS.mem_spec in H.
    Qed.

    Lemma wf_universe_subst_instance:
      forall (univs : universes_decl) (u u' : Instance.t) (l : Level.t),
        wf Σ ->
        on_udecl_prop Σ univs ->
        wf_universe (Σ.1, univs) (Universe.make' l) -> wf_instance Σ u ->
        wf_universe Σ (Universe.make' l@[u]).
    Proof using Type.
      intros ????? onu wfl wfu. red in wfl |- *; intros l' ?.
      inversion H; subst; try inversion H1. cbn in *. clear H.
      have Hin: LevelSet.In l (global_ext_levels (Σ.1, univs)).
      { specialize (wfl (l, 0)). cbn in wfl. apply wfl.
        apply LevelExprSetDecide.MSetDecideTestCases.test_In_singleton. }
      clear wfl. destruct l.
      - apply global_ext_levels_InSet.
      - apply monomorphic_level_in_global_ext in Hin. now apply LevelSetFact.union_3.
      - apply in_var_global_ext in Hin; auto. cbn in Hin.
        destruct wfu as [_ wfu]. cbn. rewrite nth_nth_error.
        destruct (nth_error (Instance.universes u) n) eqn:e.
        2: { apply global_ext_levels_InSet. }
        destruct t. apply global_ext_levels_InSet.
        -- eapply Forall_In in wfu; eauto.
           eapply nth_error_In; eauto.
        -- eapply Forall_In in wfu; eauto.
           eapply nth_error_In; eauto.
    Qed.

    Definition on_binder_annot fq (na : aname) :=
      on_relevance fq true na.(binder_relevance).

    Definition on_instance fq fu ui :=
      forallb fq (Instance.qualities ui) &&
      forallb fu (map Universe.make' (Instance.universes ui)).

    Definition on_decl_universes (ft : term -> bool) (fq : Quality.t -> bool) (fu : Universe.t -> bool) d :=
      on_binder_annot (fq ∘ Quality.qVar) d.(decl_name) &&
      option_default ft d.(decl_body) true &&
      ft d.(decl_type).

    Definition on_ctx_universes (ft : term -> bool) (fq : Quality.t -> bool) (fu : Universe.t -> bool) Γ :=
      forallb (on_decl_universes ft fq fu) Γ.

    Fixpoint on_universes fq fu fc t :=
      match t with
      | tSort s => Sort.on_sort (fq ∘ Quality.qVar) fu true andb s
      | tApp t u => on_universes fq fu fc t && on_universes fq fu fc u
      | tProd na t u
      | tLambda na t u => on_binder_annot (fq ∘ Quality.qVar) na && on_universes fq fu fc t && on_universes fq fu fc u
      | tCase ci p c brs =>
        [&&
        on_relevance (fq ∘ Quality.qVar) true ci.(ci_relevance),
        on_instance fq fu p.(puinst),
        forallb (on_universes fq fu fc) p.(pparams) ,
        fc p.(puinst) p.(pcontext),
        on_universes fq fu fc p.(preturn) ,
        on_universes fq fu fc c &
        forallb (fun br => fc p.(puinst) br.(bcontext) && on_universes fq fu fc br.(bbody)) brs]
      | tLetIn na t t' u =>
        [&& on_binder_annot (fq ∘ Quality.qVar) na,
          on_universes fq fu fc t , on_universes fq fu fc t' & on_universes fq fu fc u]
      | tProj _ t => on_universes fq fu fc t
      | tFix mfix _ | tCoFix mfix _ =>
        forallb (fun d => on_binder_annot (fq ∘ Quality.qVar) d.(dname) && on_universes fq fu fc d.(dtype) && on_universes fq fu fc d.(dbody)) mfix
      | tConst _ u | tInd _ u | tConstruct _ _ u =>
        on_instance fq fu u
      | tEvar _ args => forallb (on_universes fq fu fc) args
      | tPrim p => test_primu (fun x => fu (Universe.make' x)) (on_universes fq fu fc) p
      | _ => true
      end.

    Definition wf_ctx_inner u :=
      let q := #|Instance.qualities u| in let u := #|Instance.universes u| in
      on_ctx_universes (fun t => closedq q t && closedu u t) (closedq_quality q) (closedu_universe u).

    Definition wf_universes t := on_universes (wf_qualityb Σ) wf_universeb wf_ctx_inner t.
    Definition wf_sortb s := Sort.on_sort (wf_qvarb Σ) wf_universeb true andb s.
    Definition wf_relb r := on_relevance (wf_qvarb Σ) true r.
    Definition wf_anameb na := on_binder_annot (wf_qvarb Σ) na.

    Definition wf_decl_universes := on_decl_universes wf_universes (wf_qualityb Σ) wf_universeb.
    Definition wf_ctx_universes := forallb wf_decl_universes.

    Lemma on_instance_reflect ui :
      reflect (wf_instance Σ ui) (on_instance (wf_qualityb Σ) wf_universeb ui).
    Proof.
      unfold on_instance. rewrite forallb_map.
      apply andPP; apply forallbP => x.
    - apply wf_qualityP.
    - apply iff_reflect.
      rewrite -/(is_true _) -(rwP wf_universe_reflect).
      split.
      + intros H x' Hin.
        unfold Universe.make' in Hin.
        apply LevelExprSet.singleton_spec in Hin as ->. cbn. assumption.
      + move/(_ (LevelExpr.make x)).
        apply. by apply LevelExprSet.singleton_spec.
    Qed.

    Lemma wf_sort_reflect {s : sort} :
      reflect (wf_sort Σ s) (wf_sortb s).
    Proof using Type.
      destruct s => //=; repeat constructor.
      - apply wf_universe_reflect.
      - apply andPP.
        + apply wf_qvarP.
        + apply wf_universe_reflect.
    Qed.

    Lemma on_relevance_reflect r :
      reflect (wf_relevance Σ r) (on_relevance (wf_qvarb Σ) true r).
    Proof.
      destruct r => //=; try by constructor.
      apply wf_qvarP.
    Qed.

    Lemma on_binder_annot_reflect na :
      reflect (wf_aname Σ na) (on_binder_annot (wf_qvarb Σ) na).
    Proof.
      apply on_relevance_reflect.
    Qed.

    Lemma wf_universeb_instance_forall u :
      forallb wf_universeb (map Universe.make' u) = forallb (wf_levelb Σ) u.
    Proof using Type.
      induction u => //=.
      rewrite IHu.
      f_equal.
      cbn.
      now rewrite if_true_false.
    Qed.

    Lemma wf_relevance_subst_instance u r :
      wf Σ ->
      wf_instance Σ u ->
      wf_relevance Σ (subst_instance u r).
    Proof.
      intros wfΣ wfui.
      destruct r => //=.
      eapply wf_quality_subst_instance_qvar with (qv := t) in wfui; tea.
      cbn. destruct subst_instance_qvar => //.
    Qed.

    Lemma wf_aname_subst_instance u na :
      wf Σ ->
      wf_instance Σ u ->
      wf_aname Σ (subst_instance u na).
    Proof.
      intros wfΣ wfui.
      by apply wf_relevance_subst_instance.
    Qed.

    (* Lemma All_forallb {A} (P : A -> Type) l (H : All P l) p p' : (forall x, P x -> p x = p' x) -> forallb p l = forallb p' l.
    Proof.
      intros; induction H; simpl; auto.
      now rewrite IHAll H0.
    Qed. *)

    Lemma test_context_mapi (p : term -> bool) f (ctx : context) k :
      test_context p (mapi_context (shiftf f k) ctx) = test_context_k (fun k => p ∘ f k) k ctx.
    Proof using Type.
      induction ctx; simpl; auto.
      rewrite IHctx. f_equal.
      now rewrite test_decl_map_decl.
    Qed.
    Hint Rewrite test_context_mapi : map.

    Lemma test_context_k_ctx (p : term -> bool) (ctx : context) k :
      test_context p ctx = test_context_k (fun k => p) k ctx.
    Proof using Type.
      induction ctx; simpl; auto.
    Qed.

    Lemma on_universes_lift pq pu pc n k t : on_universes pq pu pc (lift n k t) = on_universes pq pu pc t.
    Proof using Type.
      induction t in n, k |- * using term_forall_list_ind; simpl ; auto ; try
        rewrite ?IHt1 ?IHt2 ?IHt3; auto.
      - solve_all.
      - destruct X as [? [? ?]]. solve_all.
        rewrite IHt.
        f_equal.
        f_equal.
        f_equal ; [now solve_all|..].
        f_equal.
        f_equal ; [now rewrite /id e|..].
        f_equal; solve_all; rewrite /test_branch b; f_equal.
      - rewrite forallb_map.
        eapply All_forallb_eq_forallb; eauto. simpl; intros [].
        simpl. intros. cbn. now rewrite H.
      - rewrite forallb_map.
        eapply All_forallb_eq_forallb; eauto. simpl; intros [].
        simpl. intros. cbn. now rewrite H.
      - rewrite test_primu_mapu; eapply test_primu_primProp; tea; eauto.
    Qed.

    Corollary wf_universes_lift n k t : wf_universes (lift n k t) = wf_universes t.
    Proof using Type.
      by apply on_universes_lift.
    Qed.

    Lemma on_universes_subst s k pq pu pc t :
      All (on_universes pq pu pc) s ->
      on_universes pq pu pc (subst s k t) = on_universes pq pu pc t.
    Proof using Type.
      intros Hs.
      induction t in k |- * using term_forall_list_ind; simpl; auto; try
        rewrite ?IHt1 ?IHt2 ?IHt3; auto.
      - destruct (Nat.leb_spec k n); auto.
        destruct nth_error eqn:nth; simpl; auto.
        eapply nth_error_all in nth; eauto.
        simpl in nth. intros. now rewrite on_universes_lift.
      - solve_all.
      - destruct X as [? [? ?]]. solve_all.
        rewrite IHt.
        f_equal.
        f_equal.
        f_equal ; [now solve_all|..].
        f_equal.
        f_equal ; [now rewrite /id e|..].
        f_equal; solve_all; rewrite /test_branch b; f_equal.
      - rewrite forallb_map.
        eapply All_forallb_eq_forallb; eauto. simpl; intros [].
        simpl. intros. cbn. now rewrite H.
      - rewrite forallb_map.
        eapply All_forallb_eq_forallb; eauto. simpl; intros [].
        simpl. intros. cbn. now rewrite H.
      - rewrite test_primu_mapu; eapply test_primu_primProp; tea; eauto.
    Qed.

    Corollary wf_universes_subst s k t :
      All wf_universes s ->
      wf_universes (subst s k t) = wf_universes t.
    Proof using Type.
      by apply on_universes_subst.
    Qed.

  End WfUniverses.
  Arguments wf_universe_reflect {Σ u}.

  Ltac to_prop :=
    repeat match goal with
    | [ H: is_true (?x && ?y) |- _ ] =>
     let x := fresh in let y := fresh in move/andP: H; move=> [x y]; rewrite ?x ?y; simpl
    end.

  Ltac to_wfu :=
    repeat match goal with
    | [ H: is_true (wf_qualityb _ ?x) |- _ ] => apply (elimT (@wf_qualityP _ x)) in H
    | [ |- is_true (wf_qualityb _ ?x) ] => apply (introT (@wf_qualityP _ x))
    | [ H: is_true (wf_universeb _ ?x) |- _ ] => apply (elimT (@wf_universe_reflect _ x)) in H
    | [ |- is_true (wf_universeb _ ?x) ] => apply (introT (@wf_universe_reflect _ x))
    | [ H: is_true (Sort.on_sort _ (wf_universeb _) _ _ ?x) |- _ ] => apply (elimT (@wf_sort_reflect _ x)) in H
    | [ |- is_true (Sort.on_sort _ (wf_universeb _) _ _ ?x) ] => apply (introT (@wf_sort_reflect _ x))
    | [ H: is_true (wf_sortb _ ?x) |- _ ] => apply (elimT (@wf_sort_reflect _ x)) in H
    | [ |- is_true (wf_sortb _ ?x) ] => apply (introT (@wf_sort_reflect _ x))
    | [ H: is_true (on_instance (wf_qualityb _) (wf_universeb _) ?x) |- _ ] => apply (elimT (@on_instance_reflect _ x)) in H
    | [ |- is_true (on_instance (wf_qualityb _) (wf_universeb _) ?x) ] => apply (introT (@on_instance_reflect _ x))
    | [ H: is_true (on_relevance _ _ ?x) |- _ ] => apply (elimT (@on_relevance_reflect _ x)) in H
    | [ |- is_true (on_relevance _ _ ?x) ] => apply (introT (@on_relevance_reflect _ x))
    | [ H: is_true (on_binder_annot _ ?x) |- _ ] => apply (elimT (@on_binder_annot_reflect _ x)) in H
    | [ |- is_true (on_binder_annot _ ?x) ] => apply (introT (@on_binder_annot_reflect _ x))
    end.

  Lemma wf_universes_inst {Σ : global_env_ext} univs t u :
    wf Σ ->
    on_udecl_prop Σ.1 univs ->
    wf_instance Σ u  ->
    wf_universes (Σ.1, univs) t ->
    wf_universes Σ (subst_instance u t).
  Proof using Type.
    intros wfΣ onudecl cu wft.
    induction t using term_forall_list_ind.
    all: simpl in *; auto.
    all: cbn -[Universe.make' wf_qualityb] in *.
    all: to_prop.
    all: rtoProp; repeat match goal with |- _ /\ _ => apply conj end.
    all: to_wfu; eauto using wf_instance_subst_instance, wf_sort_instantiate, wf_relevance_subst_instance, wf_aname_subst_instance.
    all: try solve [ solve_all;
      to_wfu;
      eauto using wf_aname_subst_instance
    ].
    - rewrite !length_map //.
    - solve_all.
      rewrite /wf_ctx_inner !length_map //.
    - solve_all.
      rewrite -subst_instance_universe_make. to_wfu.
      eapply (wf_universe_subst_instance_univ (Σ.1, univs)) => //.
  Qed.

  Lemma weaken_wf_universe Σ Σ' t : wf Σ' -> extends Σ.1 Σ' ->
    wf_universe Σ t ->
    wf_universe (Σ', Σ.2) t.
  Proof using Type.
    intros wfΣ ext.
    intros Hl l inl; specialize (Hl l inl).
    apply LS.union_spec. apply LS.union_spec in Hl as [Hl|Hl]; simpl.
    left; auto.
    right. now eapply global_levels_sub; [apply ext|].
  Qed.

  Lemma weaken_wf_quality Σ Σ' t : wf Σ' -> extends Σ.1 Σ' ->
    wf_quality Σ t ->
    wf_quality (Σ', Σ.2) t.
  Proof using Type.
    intros wfΣ ext Hl.
    apply QualitySet.union_spec.
    apply QualitySet.union_spec in Hl as [Hl|Hl]; eauto.
  Qed.

  Lemma weaken_wf_sort Σ Σ' t : wf Σ' -> extends Σ.1 Σ' ->
    wf_sort Σ t ->
    wf_sort (Σ', Σ.2) t.
  Proof using Type.
    destruct t => //=.
    - apply weaken_wf_universe.
    - intros ??[]; split.
      + by apply weaken_wf_quality.
      + by apply weaken_wf_universe.
  Qed.

  Lemma weaken_wf_level {Σ : global_env_ext} Σ' t : wf Σ -> wf Σ' -> extends Σ Σ' ->
    wf_level Σ t ->
    wf_level (Σ', Σ.2) t.
  Proof using Type.
    intros wfΣ wfΣ' ext.
    unfold wf_level.
    destruct t; simpl; auto using global_ext_levels_InSet;
    intros; apply LS.union_spec.
    - eapply LS.union_spec in H as [H|H].
      left; auto.
      right; auto. simpl.
      eapply global_levels_sub. apply ext. apply H.
    - cbn. eapply in_var_global_ext in H; eauto.
  Qed.

  Lemma weaken_wf_instance {Σ : global_env_ext} Σ' t : wf Σ -> wf Σ' -> extends Σ.1 Σ' ->
    wf_instance Σ t ->
    wf_instance (Σ', Σ.2) t.
  Proof using Type.
    intros wfΣ wfΣ' ext.
    intros [wfq wfu]; split; eapply Forall_impl; eauto.
    intros. now eapply weaken_wf_level.
  Qed.

  Arguments Universe.make' : simpl never.
  Lemma test_primu_test_primu_tPrimProp {P : term -> Type} {pu put} {pu' : Level.t -> bool} {put' : term -> bool} p :
    tPrimProp P p -> test_primu pu put p ->
    (forall u, pu u -> pu' u) ->
    (forall t, P t -> put t -> put' t) ->
    test_primu pu' put' p.
  Proof.
    intros hp ht hf hg.
    destruct p as [? []]; cbn => //.
    destruct a; destruct hp; cbn in *.
    rtoProp. destruct p0. intuition eauto.
    eapply forallb_All in H2. eapply All_prod in a; tea.
    eapply All_forallb, All_impl; tea. intuition eauto. apply hg; intuition auto.
  Qed.

  Lemma weaken_wf_universes {Σ : global_env_ext} Σ' t : wf Σ -> wf Σ' -> extends Σ.1 Σ' ->
    wf_universes Σ t ->
    wf_universes (Σ', Σ.2) t.
  Proof using Type.
    intros wfΣ wfΣ' ext wft.
    induction t using term_forall_list_ind.
    all: simpl in *; auto.
    all: cbn -[Universe.make' wf_qualityb] in *.
    all: to_prop.
    all: rtoProp; repeat match goal with |- _ /\ _ => apply conj end.
    all: to_wfu; eauto.
    all: try solve [ solve_all ].
  - rewrite -/(wf_sortb _ s) in wft.
    rewrite -/(wf_sortb _ s).
    to_wfu.
    now apply weaken_wf_sort.
  - eapply weaken_wf_instance ; tea.
  - eapply weaken_wf_instance ; tea.
  - eapply weaken_wf_instance ; tea.
  - eapply weaken_wf_instance ; tea.
  - eapply test_primu_test_primu_tPrimProp; tea; cbn; eauto.
    intros; to_wfu; now eapply weaken_wf_universe.
  Qed.

  Lemma wf_universes_weaken_full :
    weaken_env_prop_full cumulSpec0 (lift_typing typing)
      (fun Σ _ t T => wf_universes Σ t && wf_universes Σ T).
  Proof using Type.
    do 2 red. intros.
    to_prop; apply /andP; split; now apply weaken_wf_universes.
  Qed.

  Lemma wf_universes_weaken :
    weaken_env_prop cumulSpec0 (lift_typing typing)
      (fun Σ _ j => lift_wfbu_term (wf_universes Σ) (wf_sortb Σ) (wf_relb Σ) j).
  Proof using Type.
    intros Σ Σ' φ wfΣ wfΣ' Hext _ j Hj.
    pose proof (fun t => @weaken_wf_universes (Σ, φ) Σ' t wfΣ wfΣ' Hext).
    unfold lift_wfbu_term in *.
    rtoProp; repeat split; auto.
    + destruct j_term => //; cbn in *; auto.
    + destruct j_univ => //; cbn in *; now apply (H (tSort _)).
  Qed.

  Lemma wf_universes_inds Σ mind u bodies :
    wf_instance Σ u ->
    All (fun t : term => wf_universes Σ t) (inds mind u bodies).
  Proof using Type.
    intros wfi.
    unfold inds.
    generalize #|bodies|.
    induction n; simpl; auto.
    constructor; auto.
    cbn. by to_wfu.
  Qed.

  Lemma wf_universes_mkApps Σ f args :
    wf_universes Σ (mkApps f args) = wf_universes Σ f && forallb (wf_universes Σ) args.
  Proof using Type.
    induction args using rev_ind; simpl; auto. now rewrite andb_true_r.
    now rewrite mkApps_app forallb_app /= andb_true_r andb_assoc -IHargs.
  Qed.

  Lemma type_local_ctx_wf Σ Γ Δ s : type_local_ctx (fun Σ _ => lift_wf_term (fun t => wf_universes Σ t)) Σ Γ Δ s ->
      All (fun d => option_default (wf_universes Σ) (decl_body d) true && wf_universes Σ (decl_type d)) Δ.
  Proof using Type.
    induction Δ as [|[na [b|] ty] ?]; simpl.
    1: constructor.
    all: intros [X [Hb Ht]]; constructor; cbn; auto.
  Qed.

  Lemma consistent_instance_ext_wf Σ univs u : consistent_instance_ext Σ univs u ->
    wf_instance Σ u.
  Proof using Type.
    destruct univs; simpl.
    - destruct u as [qs us]. destruct qs, us => /= //; intros []; congruence.
    - intros (H%forallb_Forall & H' & H''%forallb_Forall & H''' & H''''). split; eapply Forall_impl; eauto; simpl; intros.
      * now eapply QualitySet.mem_spec in H0.
      * now eapply LS.mem_spec in H0.
  Qed.

  Ltac specIH :=
    repeat match goal with
    | [ H : on_udecl _ _, H' : on_udecl _ _ -> _ |- _ ] => specialize (H' H)
    end.

  Local Lemma wf_universes_local_ctx_smash (Σ : global_env_ext) mdecl args sorts :
    sorts_local_ctx (fun Σ _ => lift_wfbu_term (fun t => wf_universes Σ t) (wf_sortb Σ) (wf_relb Σ))
      (Σ.1, ind_universes mdecl) (arities_context (ind_bodies mdecl),,, ind_params mdecl) args sorts ->
    sorts_local_ctx (fun Σ _ => lift_wfbu_term (fun t => wf_universes Σ t) (wf_sortb Σ) (wf_relb Σ))
      (Σ.1, ind_universes mdecl) (arities_context (ind_bodies mdecl),,, ind_params mdecl) (smash_context [] args) sorts.
  Proof using Type.
    induction args as [|[na [b|] ty] args] in sorts |- *; simpl; auto.
    intros [X Hj].
    rewrite subst_context_nil. auto.
    destruct sorts as [|u]; auto.
    intros [X Hj].
    rewrite smash_context_acc /=. split. eauto.
    apply lift_wfbu_term_f_impl with (f := fun t => _ (_ t)) (1 := Hj) (fu := id) (fr := id) => // t Ht.
    rewrite wf_universes_subst.
    clear -X. generalize 0.
    induction args as [|[na [b|] ty] args] in sorts, X |- *; simpl in *; auto.
    - destruct X as [? Hj].
      constructor; eauto.
      rewrite wf_universes_subst. eapply IHargs; eauto.
      move: Hj => /andP[] /andP[] /andP[] /= Htm _ _ _.
      now rewrite wf_universes_lift.
    - destruct sorts => //. destruct X.
      constructor => //. eapply IHargs; eauto.
    - now rewrite wf_universes_lift.
  Qed.

  Lemma wf_universes_local_ctx_nth_error Σ P Pu Pr Γ Δ s n d :
    sorts_local_ctx (fun Σ _ => lift_wfbu_term (P Σ) (Pu Σ) (Pr Σ)) Σ Γ Δ s ->
    nth_error Δ n = Some d ->
    P Σ (decl_type d).
  Proof using Type.
    induction Δ as [|[na [b|] ty] Δ] in n, s |- *; simpl; auto.
    - now rewrite nth_error_nil.
    - move => [] h /andP[] /andP[] /andP[] _ h' _ _.
      destruct n. simpl. move=> [= <-] //=.
      now simpl; eapply IHΔ.
    - destruct s => //. move => [] h /andP[] /andP[] /andP[] _ h' _ _.
      destruct n. simpl. move=> [= <-] //=.
      now simpl; eapply IHΔ.
  Qed.

  Lemma wf_abstract_instance Σ decl :
    wf_instance (Σ, decl) (abstract_instance decl).
  Proof using Type.
    destruct decl as [|[u cst]]=> /=.
    split; cbn; apply Forall_nil.
    red. split; cbn; rewrite mapi_unfold; eapply All_Forall, All_unfold.
    - intros q hin.
      red. eapply QualitySet.union_spec; left. simpl.
      rewrite /AUContext.qualities /= mapi_unfold.
      eapply QualitySetProp.of_list_1.
      apply SetoidList.InA_alt.
      exists (Quality.var q); split; cbnr.
      apply In_unfold; eauto.
    - intros l hin.
      red. eapply LS.union_spec; left. simpl.
      rewrite /AUContext.levels /= mapi_unfold.
      eapply LevelSetProp.of_list_1.
      apply SetoidList.InA_alt.
      exists (Level.lvar l); split; cbnr.
      apply In_unfold; eauto.
  Qed.

  Lemma wf_universes_it_mkProd_or_LetIn {Σ Γ T} :
    wf_universes Σ (it_mkProd_or_LetIn Γ T) = wf_ctx_universes Σ Γ && wf_universes Σ T.
  Proof using Type.
    induction Γ as [ |[na [b|] ty] Γ] using rev_ind ; simpl; auto;
    rewrite it_mkProd_or_LetIn_app {1}/wf_universes /=
    -!/(wf_universes _ _) IHΓ /wf_ctx_universes forallb_app /=
    {3}/wf_decl_universes -!/(wf_universes _ _) / on_decl_universes /= /wf_universes ?andb_true_r;
    repeat bool_congr.

  Qed.

  Lemma wf_universes_it_mkLambda_or_LetIn {Σ Γ T} :
    wf_universes Σ (it_mkLambda_or_LetIn Γ T) = wf_ctx_universes Σ Γ && wf_universes Σ T.
  Proof using Type.
    induction Γ as [ |[na [b|] ty] Γ] using rev_ind; simpl; auto;
    now rewrite it_mkLambda_or_LetIn_app {1}/wf_universes /=
    -!/(wf_universes _ _) IHΓ /wf_ctx_universes forallb_app /=
    {3}/wf_decl_universes -!/(wf_universes _ _) / on_decl_universes /= /wf_universes ?andb_true_r;
    repeat bool_congr.
  Qed.

  Lemma wf_projs Σ ind npars p :
    All (fun t : term => wf_universes Σ t) (projs ind npars p).
  Proof using Type.
    induction p; simpl; auto.
  Qed.

  Lemma wf_extended_subst Σ Γ n :
    wf_ctx_universes Σ Γ ->
    All (fun t : term => wf_universes Σ t) (extended_subst Γ n).
  Proof using Type.
    induction Γ as [|[na [b|] ty] Γ] in n |- *; simpl; auto.
    - rewrite /wf_decl_universes/on_decl_universes /= => /andP[]/andP[]/andP[] wfna wfb wfty wfΓ.
      constructor; eauto. rewrite wf_universes_subst //. 1:now apply IHΓ.
      now rewrite wf_universes_lift.
    - rewrite /wf_decl_universes/on_decl_universes /= => /andP[]/andP[]wfna wfty wfΓ.
      constructor; eauto.
  Qed.

  Lemma closedu_compare_decls k Γ Δ :
    PCUICEquality.eq_context_upto_names Γ Δ ->
    test_context (closedu k) Γ = test_context (closedu k) Δ.
  Proof using Type.
    induction 1; cbn; auto.
    f_equal; auto. destruct r; subst; auto.
  Qed.

  Lemma wf_ctx_inner_compare_decls ui Γ Δ :
    PCUICEquality.eq_context_upto_names Γ Δ ->
    wf_ctx_inner ui Γ = wf_ctx_inner ui Δ.
  Proof using Type.
    induction 1; cbn; auto.
    f_equal; auto. unfold on_decl_universes, on_binder_annot.
    destruct r; subst; cbn; auto.
    all: destruct e; auto.
  Qed.

  Lemma wf_ctx_inner_lengths ui ui' Γ :
    #|Instance.qualities ui| = #|Instance.qualities ui'| ->
    #|Instance.universes ui| = #|Instance.universes ui'| ->
    wf_ctx_inner ui Γ = wf_ctx_inner ui' Γ.
  Proof using Type.
    unfold wf_ctx_inner.
    by intros <- <-.
  Qed.

  Lemma closedq_mkApps k f args : closedq k (mkApps f args) = closedq k f && forallb (closedq k) args.
  Proof using Type.
    induction args in f |- *; cbn; auto. ring.
    rewrite IHargs /=. ring.
  Qed.

  Lemma closedu_mkApps k f args : closedu k (mkApps f args) = closedu k f && forallb (closedu k) args.
  Proof using Type.
    induction args in f |- *; cbn; auto. ring.
    rewrite IHargs /=. ring.
  Qed.

  Lemma closedq_abstract_instance univs :
    closed_instance_qualities #|Instance.qualities (abstract_instance univs)|
    (abstract_instance univs).
  Proof using Type.
    destruct univs as [|[l csts]] => // /=.
    rewrite /UContext.instance /AUContext.repr.
    rewrite /closed_instance_qualities !forallb_mapi //.
    intros i hi; cbn; len; now eapply Nat.ltb_lt.
  Qed.

  Lemma closedu_abstract_instance univs :
    closed_instance_universes #|Instance.universes (abstract_instance univs)|
    (abstract_instance univs).
  Proof using Type.
    destruct univs as [|[l csts]] => // /=.
    rewrite /UContext.instance /AUContext.repr.
    rewrite /closed_instance_universes !forallb_mapi //.
    intros i hi; cbn; len; now eapply Nat.ltb_lt.
  Qed.

  Notation closedq_ctx_weak k := (test_context (closedq k)).
  Notation closedu_ctx k := (test_context (closedu k)).

  Lemma closedq_lift k n k' t :
    closedq k (lift n k' t) = closedq k t.
  Proof using Type.
    induction t in k' |- * using term_forall_list_ind; cbn; auto; intros; solve_all.
    - rewrite IHt.
      rewrite /map_predicate_k /= /test_predicate /test_predicate_kq /= /id.
      f_equal. f_equal. rewrite e. f_equal. f_equal. f_equal.
      solve_all.
      solve_all.
      all: rewrite /map_branch_k /test_branch /=; f_equal;
        now rewrite b.
    - rewrite /test_def/test_def_gen /map_def /=. now rewrite b b0.
    - rewrite /test_def/test_def_gen /map_def /=. now rewrite b b0.
    - rewrite !test_primq_test_prim -!test_primu_test_prim test_primu_mapu; eapply test_primu_primProp; tea; eauto.
  Qed.

  Lemma closedu_lift k n k' t :
    closedu k (lift n k' t) = closedu k t.
  Proof using Type.
    induction t in k' |- * using term_forall_list_ind; cbn; auto; intros; solve_all.
    - rewrite IHt.
      rewrite /map_predicate_k /= /test_predicate /test_predicate_ku /= /id.
      f_equal. f_equal. rewrite e. f_equal. f_equal. f_equal.
      solve_all.
      solve_all.
      all: rewrite /map_branch_k /test_branch /=; f_equal;
        now rewrite b.
    - rewrite /test_def /map_def /=. now rewrite b b0.
    - rewrite /test_def /map_def /=. now rewrite b b0.
    - rewrite test_primu_mapu; eapply test_primu_primProp; tea; eauto.
  Qed.

  Ltac try_hyp :=
    multimatch goal with H : _ |- _ => eapply H end.

  Ltac crush := repeat (solve_all; try try_hyp; cbn).

  Lemma closedq_subst k s k' t :
    forallb (closedq k) s && closedq k t ->
    closedq k (subst s k' t).
  Proof using Type.
    induction t in k' |- * using term_forall_list_ind; cbn; auto; intros;
      try solve [ repeat (solve_all; try try_hyp) ].
    - destruct Nat.leb => //.
      destruct nth_error eqn:eq => //.
      rtoProp.
      rewrite closedq_lift.
      eapply nth_error_forallb in eq; tea.
    - unfold test_predicate_kq in *. unfold test_branch in *. crush.
    - unfold test_def, test_def_gen in *; crush.
    - unfold test_def, test_def_gen in *; crush.
    - move/andP: H => [].
      rewrite !test_primq_test_prim -!test_primu_test_prim.
      crush.
  Qed.

  Lemma closedu_subst k s k' t :
    forallb (closedu k) s && closedu k t ->
    closedu k (subst s k' t).
  Proof using Type.
    Ltac t := repeat (solve_all; try try_hyp).
    induction t in k' |- * using term_forall_list_ind; cbn; auto; intros;
      try solve [t].
    - destruct Nat.leb => //.
      destruct nth_error eqn:eq => //.
      rewrite closedu_lift.
      eapply nth_error_forallb in eq; tea. solve_all.
    - unfold test_predicate_ku in *. unfold test_branch in *. crush.
    - unfold test_def in *; crush.
    - unfold test_def in *; crush.
  Qed.

  Lemma wf_ctx_inner_subst_context ui s k Γ :
    forallb (fun t => closedq #|Instance.qualities ui| t && closedu #|Instance.universes ui| t) s &&
    wf_ctx_inner ui Γ ->
    wf_ctx_inner ui (subst_context s k Γ).
  Proof.
    rewrite /subst_context.
    move=> /andP [] Hs.
    induction Γ.
    * cbn; auto.
    * move=> /=/andP[] Ha HΓ. forward IHΓ by assumption.
      rewrite fold_context_k_snoc0 /= IHΓ // andb_true_r.
      unfold on_decl_universes, map_decl, map_decl_gen, id in *; cbn -[closedq_quality].
      rtoProp; split; [split|]; tas.
      + destruct decl_body; cbnr. cbn in H2.
        rewrite closedq_subst ?closedu_subst //.
        all: solve_all.
      + rewrite closedq_subst ?closedu_subst //.
        all: solve_all.
  Qed.

  Lemma closedu_subst_context k s k' Γ :
    forallb (closedu k) s && closedu_ctx k Γ ->
    closedu_ctx k (subst_context s k' Γ).
  Proof using Type.
    rewrite /subst_context.
    induction Γ.
    * cbn; auto.
    * rtoProp. intros []. cbn in H0. rtoProp.
      rewrite fold_context_k_snoc0 /= IHΓ //. crush.
      unfold test_decl in *. crush.
      destruct decl_body eqn:heq => /= //.
      rewrite closedu_subst //. crush.
      rewrite closedu_subst //. crush.
  Qed.

  Lemma wf_ctx_inner_lift_context ui n k Γ :
    wf_ctx_inner ui (lift_context n k Γ) =
    wf_ctx_inner ui Γ.
  Proof.
    unfold lift_context.
    induction Γ.
    * cbn; auto.
    * rewrite /= fold_context_k_snoc0 /=. f_equal; tas.
      unfold on_decl_universes, map_decl, map_decl_gen, id in *; cbn -[closedq_quality].
      f_equal. 1:f_equal; tas.
      + destruct decl_body; cbnr.
        rewrite closedq_lift closedu_lift //.
      + rewrite closedq_lift closedu_lift //.
  Qed.

  Lemma closedu_lift_context k n k' Γ :
    closedu_ctx k (lift_context n k' Γ) = closedu_ctx k Γ.
  Proof using Type.
    rewrite /lift_context.
    induction Γ.
    * cbn; auto.
    * rtoProp.
      rewrite fold_context_k_snoc0 /= IHΓ //.
      unfold test_decl in *.
      cbn.
      rewrite closedu_lift.
      destruct (decl_body a) => /= //.
      rewrite closedu_lift //.
  Qed.

  Lemma closedqu_extended_subst ui Γ k :
    wf_ctx_inner ui Γ ->
    forallb (fun t => closedq #|Instance.qualities ui| t && closedu #|Instance.universes ui| t) (extended_subst Γ k).
  Proof using Type.
    intro H. move H after k.
    induction Γ in H, k |- *; cbn; auto.
    move: H =>/=/andP[] Ha HΓ. forward IHΓ by assumption.
    unfold on_decl_universes in Ha.
    destruct a as [na [b|] ty]; cbn in Ha |- *.
    all: rewrite IHΓ //= andb_true_r.
    rtoProp; split.
    - apply closedq_subst.
      rewrite closedq_lift.
      rtoProp; split; tas.
      specialize (IHΓ k).
      solve_all.
    - apply closedu_subst.
      rewrite closedu_lift.
      rtoProp; split; tas.
      specialize (IHΓ k).
      solve_all.
  Qed.

  Lemma closedu_extended_subst k Γ k' :
    closedu_ctx k Γ ->
    forallb (closedu k) (extended_subst Γ k').
  Proof using Type.
    induction Γ in k' |- *; cbn; auto. destruct a as [na [b|] ty] => /= //.
    unfold test_decl; move/andP=> [] clΓ /= cld. apply/andP. split.
    eapply closedu_subst. rewrite IHΓ // /= closedu_lift. crush.
    now rewrite IHΓ.
    unfold test_decl; move/andP=> [] clΓ /= cld. now apply IHΓ.
  Qed.

  Lemma wf_ctx_inner_expand_lets_ctx ui Γ Δ :
    wf_ctx_inner ui Γ && wf_ctx_inner ui Δ ->
    wf_ctx_inner ui (expand_lets_ctx Γ Δ).
  Proof using Type.
    rewrite /expand_lets_ctx /expand_lets_k_ctx.
    move/andP => [] clΓ clΔ.
    apply wf_ctx_inner_subst_context.
    rewrite closedqu_extended_subst // /= wf_ctx_inner_lift_context //.
  Qed.

  Lemma closedu_expand_lets_ctx k Γ Δ :
    closedu_ctx k Γ && closedu_ctx k Δ ->
    closedu_ctx k (expand_lets_ctx Γ Δ).
  Proof using Type.
    rewrite /expand_lets_ctx /expand_lets_k_ctx.
    move/andP => [] clΓ clΔ.
    apply closedu_subst_context.
    rewrite closedu_extended_subst // /= closedu_lift_context //.
  Qed.

  Lemma wf_ctx_inner_smash_context_gen ui Γ Δ :
    wf_ctx_inner ui Γ -> wf_ctx_inner ui Δ ->
    wf_ctx_inner ui (smash_context Γ Δ).
  Proof using Type.
    induction Δ in Γ |- *; cbn; auto.
    move=> clΓ /andP[] cla clΔ.
    destruct a as [na [b|] ty] => //.
    - apply IHΔ => //.
      apply wf_ctx_inner_subst_context => /= //.
      now move: cla => /andP[]/andP[] /= _ -> clty.
    - apply IHΔ => //.
      rewrite /wf_ctx_inner/on_ctx_universes forallb_app/=.
      rtoProp; repeat split; tas.
  Qed.

  Lemma wf_ctx_inner_smash_context ui Δ :
    wf_ctx_inner ui Δ ->
    wf_ctx_inner ui (smash_context [] Δ).
  Proof using Type.
    apply wf_ctx_inner_smash_context_gen => //.
  Qed.

  Lemma closedu_smash_context_gen k Γ Δ :
    closedu_ctx k Γ -> closedu_ctx k Δ ->
    closedu_ctx k (smash_context Γ Δ).
  Proof using Type.
    induction Δ in Γ |- *; cbn; auto.
    move=> clΓ /andP[] clΔ cla.
    destruct a as [na [b|] ty] => //.
    - apply IHΔ => //. apply closedu_subst_context => /= //.
      now move/andP: cla => [] /= -> clty.
    - apply IHΔ => //.
      now rewrite test_context_app clΓ /= andb_true_r.
  Qed.

  Lemma closedu_smash_context k Δ :
    closedu_ctx k Δ ->
    closedu_ctx k (smash_context [] Δ).
  Proof using Type.
    apply closedu_smash_context_gen => //.
  Qed.

  Lemma wf_qvar_closed {Σ : global_env} univs q :
    wf_qvar (Σ, univs) q -> closedq_quality #|Instance.qualities (polymorphic_instance univs)| (Quality.qVar q).
  Proof using Type.
    intros Ht.
    unfold closedq_quality. destruct q.
    red in Ht. eapply in_var_global_ext' in Ht => //.
    cbn in Ht. destruct univs. inversion Ht.
    cbn in Ht. unfold AUContext.qualities in Ht.
    eapply QualitySetProp.of_list_1 in Ht.
    eapply SetoidList.InA_alt in Ht.
    destruct Ht as (q & e & Ht).
    move:e. destruct q => //=. destruct t => //=. intros <-.
    destruct cst as [names cstrs].
    unfold AUContext.repr in Ht |- *. cbn in *. len.
    rewrite mapi_unfold in Ht. eapply In_unfold in Ht as [k []].
    injection H0 as [= <-]. by apply Nat.leb_le.
  Qed.

  Lemma wf_quality_closed {Σ : global_env} univs q :
    wf_quality (Σ, univs) q -> closedq_quality #|Instance.qualities (polymorphic_instance univs)| q.
  Proof using Type.
    intros Ht; destruct q => //.
    by eapply wf_qvar_closed in Ht.
  Qed.

  Lemma wf_level_closed {Σ : global_env} {wfΣ : wf Σ} univs l :
    on_udecl_prop Σ univs ->
    wf_level (Σ, univs) l -> closedu_level #|Instance.universes (polymorphic_instance univs)| l.
  Proof using Type.
    intros ond Ht; destruct l => //.
    cbn in Ht. unfold closedu_level.
    cbn. red in Ht.
    eapply in_var_global_ext in Ht => //.
    cbn in Ht.
    destruct (udecl_prop_in_var_poly (Σ := (Σ, univs)) Ht) as [ctx eq].
    cbn in eq. subst univs.
    cbn in Ht. cbn. unfold AUContext.levels in Ht.
    eapply LevelSetProp.of_list_1 in Ht.
    eapply InA_In_eq in Ht.
    destruct ctx as [names cstrs].
    unfold AUContext.repr in Ht |- *. cbn in *. len.
    rewrite mapi_unfold in Ht. eapply In_unfold in Ht as [k []].
    eapply Nat.leb_le. noconf H0. lia.
  Qed.

  Lemma wf_universe_closed {Σ : global_env} {wfΣ : wf Σ} univs u :
    on_udecl_prop Σ univs ->
    wf_universe (Σ, univs) u -> closedu_universe #|Instance.universes (polymorphic_instance univs)| u.
  Proof using Type.
    intros ond Ht.
    cbn in Ht. unfold closedu_universe.
    eapply LevelExprSet.for_all_spec.
    intros x y ?; subst; auto.
    intros i hi. specialize (Ht i hi).
    unfold closedu_level_expr.
    apply wf_level_closed => //.
  Qed.

  Lemma wf_sort_closed {Σ : global_env} {wfΣ : wf Σ} univs s :
    on_udecl_prop Σ univs ->
    wf_sort (Σ, univs) s ->
    closedq_sort #|Instance.qualities (polymorphic_instance univs)| s /\
    closedu_sort #|Instance.universes (polymorphic_instance univs)| s.
  Proof using Type.
    destruct s => //=.
    - split => //; by apply wf_universe_closed.
    - split.
      + eapply wf_qvar_closed; apply H0.
      + by apply wf_universe_closed, H0.
  Qed.

  Lemma wf_instance_closed {Σ : global_env} {wfΣ : wf Σ} {univs u} :
    on_udecl_prop Σ univs ->
    wf_instance (Σ, univs) u ->
    closed_instance #|Instance.qualities (polymorphic_instance univs)| #|Instance.universes (polymorphic_instance univs)| u.
  Proof using Type.
    intros ond [Hq Hu].
    unfold closed_instance, closed_instance_qualities, closed_instance_universes. solve_all.
    - now eapply wf_quality_closed; tea.
    - now apply wf_level_closed.
  Qed.

  Lemma wf_instance_universes_closed {Σ : global_env} {wfΣ : wf Σ} {univs u} :
    on_udecl_prop Σ univs ->
    Forall (wf_level (Σ, univs)) (Instance.universes u) ->
    closed_instance_universes #|Instance.universes (polymorphic_instance univs)| u.
  Proof using Type.
    intros Hu. unfold closed_instance_universes. solve_all. apply wf_level_closed; auto.
  Qed.

  Lemma wf_instance_qualities_closed {Σ : global_env} {wfΣ : wf Σ} {univs u} :
    on_udecl_prop Σ univs ->
    Forall (wf_quality (Σ, univs)) (Instance.qualities u) ->
    closed_instance_qualities #|Instance.qualities (polymorphic_instance univs)| u.
  Proof using Type.
    intros Hu. unfold closed_instance_qualities. solve_all. eapply wf_quality_closed; tea.
  Qed.

  Lemma wf_universe_make Σ u : wf_universe Σ (Universe.make' u) -> wf_level Σ u.
  Proof.
    rewrite /wf_universe /= => hl; rewrite /wf_level.
    apply (hl (u, 0)). lsets.
  Qed.

  Lemma wf_relevance_closed {Σ : global_env} univs r :
    wf_relevance (Σ, univs) r -> closedq_rel #|Instance.qualities (polymorphic_instance univs)| r.
  Proof using Type.
    unfold wf_relevance, closedq_rel.
    destruct r => //=.
    apply wf_qvar_closed.
  Qed.

  Lemma wf_aname_closed {Σ : global_env} univs na :
    wf_aname (Σ, univs) na -> closedq_aname #|Instance.qualities (polymorphic_instance univs)| na.
  Proof using Type.
    apply wf_relevance_closed.
  Qed.

  Lemma wf_ctx_inner_closedq ui Γ :
    wf_ctx_inner ui Γ -> closedq_ctx_weak #|Instance.qualities ui| Γ.
  Proof.
    move/forallb_All. induction 1 => //=.
    unfold on_decl_universes, test_decl in *.
    rtoProp. split; tas. split; tas.
    destruct decl_body; cbn in *; by rtoProp.
  Qed.

  Lemma wf_ctx_inner_closedu ui Γ :
    wf_ctx_inner ui Γ -> closedu_ctx #|Instance.universes ui| Γ.
  Proof.
    move/forallb_All. induction 1 => //=.
    unfold on_decl_universes, test_decl in *.
    rtoProp. split; tas. split; tas.
    destruct decl_body; cbn in *; by rtoProp.
  Qed.

  Lemma wf_universes_closedu {Σ : global_env} {wfΣ : wf Σ} {univs t} :
    on_udecl_prop Σ univs ->
    wf_universes (Σ, univs) t -> closedu #|Instance.universes (polymorphic_instance univs)| t.
  Proof using Type.
    intros ond. induction t using term_forall_list_ind; cbn -[wf_qualityb] => //; solve_all.
    all: try (toAll; eapply All_impl; eauto; intros; apply wf_universe_make).
    all: try (now move/wf_universe_reflect in H).
    - to_wfu. apply wf_sort_closed; auto.
    - to_wfu. apply wf_instance_universes_closed; auto. apply H.
    - to_wfu. apply wf_instance_universes_closed; auto. apply H.
    - to_wfu. apply wf_instance_universes_closed; auto. apply H.
    - unfold test_predicate_ku. solve_all.
      to_wfu.
      + by eapply wf_instance_universes_closed, H.
      + by apply wf_ctx_inner_closedu.
    - unfold test_branch in *; solve_all.
      by apply wf_ctx_inner_closedu.
    - unfold test_def in *; solve_all.
    - unfold test_def in *; solve_all.
    - eapply test_primu_test_primu_tPrimProp; tea; cbn; eauto.
      intros. to_wfu. apply wf_level_closed; auto.
      now apply wf_universe_make.
  Qed.

  Lemma wf_universes_closedq {Σ : global_env} {wfΣ : wf Σ} {univs t} :
    on_udecl_prop Σ univs ->
    wf_universes (Σ, univs) t -> closedq #|Instance.qualities (polymorphic_instance univs)| t.
  Proof using Type.
    intros ond. induction t using term_forall_list_ind; cbn -[wf_qualityb] => //; solve_all.
    all: try (toAll; eapply All_impl; eauto; intros).
    all: try (now move/wf_quality_reflect in H).
    - to_wfu. apply wf_sort_closed; auto.
    - to_wfu. eapply wf_aname_closed; tea.
    - to_wfu. eapply wf_aname_closed; tea.
    - to_wfu. eapply wf_aname_closed; tea.
    - to_wfu. apply wf_instance_qualities_closed; auto. apply H.
    - to_wfu. apply wf_instance_qualities_closed; auto. apply H.
    - to_wfu. apply wf_instance_qualities_closed; auto. apply H.
    - to_wfu. eapply wf_relevance_closed; tea.
    - to_wfu. unfold test_predicate_kq. solve_all.
      + eapply wf_instance_closed in H; tas. unfold closed_instance in H. by rtoProp.
      + by eapply wf_ctx_inner_closedq.
    - unfold test_branch in *; solve_all.
      by eapply wf_ctx_inner_closedq.
    - unfold test_def, test_def_gen in *; solve_all.
      to_wfu. eapply wf_aname_closed; tea.
    - unfold test_def, test_def_gen in *; solve_all.
      to_wfu. eapply wf_aname_closed; tea.
    - rewrite test_primq_test_prim -test_primu_test_prim.
      eapply test_primu_test_primu_tPrimProp; tea; cbn; eauto.
  Qed.

  Lemma wf_ctx_universes_inner {Σ} {wfΣ : wf Σ} {univs ctx} :
    on_udecl_prop Σ univs ->
    wf_ctx_universes (Σ, univs) ctx ->
    wf_ctx_inner (polymorphic_instance univs) ctx.
  Proof using Type.
    intros ond.
    apply forallb_impl.
    move => d _ /andP[]/andP[] hna hb hty.
    to_wfu.
    apply/andP; split. 1: apply/andP; split.
    - by apply wf_aname_closed in hna.
    - destruct decl_body; cbn in *; tas.
      apply wf_universes_closedq in hb as h1; tas; rewrite h1.
      apply wf_universes_closedu in hb as h2; tas; rewrite h2.
    - apply wf_universes_closedq in hty as h1; tas; rewrite h1.
      apply wf_universes_closedu in hty as h2; tas; rewrite h2.
  Qed.

  Lemma wf_ctx_universes_closed {Σ} {wfΣ : wf Σ} {univs ctx} :
    on_udecl_prop Σ univs ->
    wf_ctx_universes (Σ, univs) ctx ->
    closedu_ctx #|Instance.universes (polymorphic_instance univs)| ctx.
  Proof using Type.
    intros ond. induction ctx => //.
    rewrite /wf_ctx_universes /= => /andP[] wfa wfctx.
    rewrite IHctx // /=.
    unfold wf_decl_universes, on_decl_universes, test_decl in *.
    revert wfa. rtoProp.
    destruct a as [na [b|] ty]; cbn -[wf_qualityb] in *.
    all: intros [[]]; split => //; eapply wf_universes_closedu; tea.
  Qed.

  Lemma closedu_reln k Γ k' acc :
    closedu_ctx k Γ ->
    forallb (closedu k) acc ->
    forallb (closedu k) (reln acc k' Γ).
  Proof using Type.
    induction Γ in acc, k' |- *; cbn; auto.
    destruct a as [na [b|] ty] => /= //.
    - unfold test_decl; move/andP=> [] clΓ /= cld. now eapply IHΓ.
    - unfold test_decl; move/andP=> [] clΓ /= cld clacc; now apply IHΓ => //.
  Qed.

  Lemma closedu_to_extended_list_k k Γ k' :
    closedu_ctx k Γ ->
    forallb (closedu k) (to_extended_list_k Γ k').
  Proof using Type.
    intros clΓ. apply closedu_reln => //.
  Qed.

  Lemma closedq_reln k Γ k' acc :
    closedq_ctx_weak k Γ ->
    forallb (closedq k) acc ->
    forallb (closedq k) (reln acc k' Γ).
  Proof using Type.
    induction Γ in acc, k' |- *; cbn; auto.
    destruct a as [na [b|] ty] => /= //.
    - unfold test_decl; move/andP=> [] clΓ /= cld. now eapply IHΓ.
    - unfold test_decl; move/andP=> [] clΓ /= cld clacc; now apply IHΓ => //.
  Qed.

  Lemma closedq_to_extended_list_k k Γ k' :
    closedq_ctx_weak k Γ ->
    forallb (closedq k) (to_extended_list_k Γ k').
  Proof using Type.
    intros clΓ. apply closedq_reln => //.
  Qed.

  Lemma closedu_ind_predicate_context {Σ ind mdecl idecl} {wfΣ : wf Σ} :
    declared_inductive Σ ind mdecl idecl ->
    closedu_ctx #|Instance.universes (polymorphic_instance (ind_universes mdecl))|
      (ind_params mdecl) ->
    closedu_ctx #|Instance.universes (polymorphic_instance (ind_universes mdecl))|
            (ind_indices idecl) ->
    test_context (closedu #|Instance.universes (abstract_instance (ind_universes mdecl))|) (ind_predicate_context ind mdecl idecl).
  Proof using Type.
    intros decli.
    rewrite /ind_predicate_context; cbn.
    rewrite closedu_mkApps /=.
    rewrite closedu_abstract_instance /= => clpars clinds.
    apply/andP; split.
    * apply closedu_expand_lets_ctx. now rewrite clpars clinds.
    * apply closedu_to_extended_list_k.
      rewrite test_context_app.
      rewrite (closedu_smash_context _ _ clpars).
      apply closedu_expand_lets_ctx => //.
      now rewrite clpars.
  Qed.

  Lemma closedu_inds {Σ ind mdecl} {wfΣ : wf Σ} :
    forallb (closedu #|Instance.universes (abstract_instance (ind_universes mdecl))|)
      (inds ind (abstract_instance (ind_universes mdecl)) (ind_bodies mdecl)).
  Proof using Type.
    rewrite /inds.
    induction #|ind_bodies mdecl|; cbn; auto.
    rewrite IHn andb_true_r.
    eapply closedu_abstract_instance.
  Qed.

  Lemma wf_ctx_subst_inds ind mdecl :
  forallb (fun t => closedq #|Instance.qualities (abstract_instance (ind_universes mdecl))| t &&
    closedu #|Instance.universes (abstract_instance (ind_universes mdecl))| t)
    (inds (inductive_mind ind) (abstract_instance (ind_universes mdecl)) (ind_bodies mdecl)).
  Proof.
      Proof.
    rewrite /inds.
    induction #|ind_bodies mdecl|; cbn; auto.
    rtoProp; repeat split; tas.
    - apply closedq_abstract_instance.
    - apply closedu_abstract_instance.
  Qed.

  Lemma wf_ctx_inner_app ui Γ Δ :
    wf_ctx_inner ui (Γ ,,, Δ) = wf_ctx_inner ui Δ && wf_ctx_inner ui Γ.
  Proof.
    apply forallb_app.
  Qed.

  Lemma wf_ctx_inner_ind_predicate_context {Σ ind mdecl idecl} {wfΣ : wf Σ} :
    declared_inductive Σ ind mdecl idecl ->
    closedq_rel #|Instance.qualities (polymorphic_instance (ind_universes mdecl))| idecl.(ind_relevance) ->
    wf_ctx_inner (polymorphic_instance (ind_universes mdecl)) (ind_params mdecl) ->
    wf_ctx_inner (polymorphic_instance (ind_universes mdecl)) (ind_indices idecl) ->
    wf_ctx_inner (abstract_instance (ind_universes mdecl)) (ind_predicate_context ind mdecl idecl).
  Proof using Type.
    intros decli.
    rewrite /ind_predicate_context/=/on_decl_universes/=/on_binder_annot/= ?andb_true_r /closedq_rel /on_relevance => -> /=.
    rewrite closedq_mkApps closedu_mkApps /=.
    rewrite closedq_abstract_instance closedu_abstract_instance /= => clpars clinds.
    have clΓ : wf_ctx_inner (polymorphic_instance (ind_universes mdecl)) (smash_context [] (ind_params mdecl),,, expand_lets_ctx (ind_params mdecl) (ind_indices idecl)).
    2:repeat (apply/andP; split).
    - rewrite wf_ctx_inner_app.
      rewrite wf_ctx_inner_smash_context //.
      rewrite wf_ctx_inner_expand_lets_ctx //.
      now rtoProp; split.
    - apply closedq_to_extended_list_k.
      by eapply wf_ctx_inner_closedq.
    - apply closedu_to_extended_list_k.
      by eapply wf_ctx_inner_closedu.
    - rewrite wf_ctx_inner_app in clΓ.
      by rtoProp.
  Qed.

  Lemma wf_ctx_inner_cstr_branch_context {Σ ind mdecl cdecl} {wfΣ : wf Σ} :
    wf_ctx_inner (polymorphic_instance (ind_universes mdecl)) (ind_params mdecl) ->
    wf_ctx_inner (polymorphic_instance (ind_universes mdecl)) (cstr_args cdecl) ->
    wf_ctx_inner (abstract_instance (ind_universes mdecl)) (cstr_branch_context ind mdecl cdecl).
  Proof using Type.
    intros clpars clargs.
    rewrite /cstr_branch_context.
    rewrite wf_ctx_inner_expand_lets_ctx // clpars /=.
    apply wf_ctx_inner_subst_context.
    rewrite wf_ctx_subst_inds/=.
    assumption.
  Qed.

  #[local] Transparent relevance_of_quality.
  Lemma isSortRel_wf_relevance Σ s r :
    isSortRel s r ->
    wf_sort Σ s ->
    wf_relevance Σ r.
  Proof.
    destruct s, r => //= [=] <- [] //.
  Qed.

  Local Transparent relevance_of_quality.
  Theorem wf_types :
    env_prop (fun Σ Γ t T => wf_universes Σ t && wf_universes Σ T)
      (fun Σ _ j => lift_wfbu_term (wf_universes Σ) (wf_sortb Σ) (wf_relb Σ) j)
      (fun Σ Γ => wf_ctx_universes Σ Γ).
  Proof using Type.
    apply typing_ind_env; unfold lift_wfbu_term; intros; rename_all_hyps;
    cbn -[wf_qualityb]; rewrite -!/(wf_sortb _ _) -!/(wf_universes _ _) ;
    specIH; to_prop;
    cbn -[wf_qualityb]; auto.

    - eapply MRReflect.introT. 1: apply lift_wfu_wfbu_term.
      apply lift_typing_subjtyp with (1 := X) => //=.
      + move => t T [] _ /andP[] //.
      + move => t s r [] _ /andP[] _ //= h e.
        destruct s, r => //=. injection e as [= <-].
        cbn -[wf_qualityb] in h.
        rtoProp. assumption.

    - apply All_local_env_cst, All_forallb in X0.
      unfold wf_ctx_universes, wf_decl_universes, on_decl_universes.
      apply forallb_impl with (2 := X0) => [] [na bo ty] _ //= /andP[]/andP[]/andP[] //=.
      intros; rtoProp; repeat split; tas.

    - rewrite wf_universes_lift.
      eapply forallb_nth_error with (n := n) in H0. rewrite heq_nth_error /= in H0.
      now move/andP: H0.

    - apply/andP; split; to_wfu; cbn ; eauto with pcuic.

    - rtoProp; repeat split; tas.
      cbn -[wf_qualityb] in *; rewrite -/(wf_sortb _ _) in H3; to_wfu ; eauto with pcuic.
    - rewrite wf_universes_subst. constructor. to_wfu; auto. constructor.
      now move/andP: H1 => [].

    - apply/andP; split; to_wfu.
      { eapply consistent_instance_ext_wf; eauto. }
      pose proof (declared_constant_inv _ _ _ _ wf_universes_weaken wf X H0) as [[[_ X0]%andb_and _]%andb_and _]%andb_and.
      unshelve eapply declared_constant_to_gen in H0; eauto.
      epose proof (weaken_lookup_on_global_env' Σ.1 _ _ wf H0).
      eapply wf_universes_inst. 2:eauto. all:eauto.
      now eapply consistent_instance_ext_wf.

    - apply/andP; split; to_wfu.
      { eapply consistent_instance_ext_wf; eauto. }
      pose proof (declared_inductive_inv wf_universes_weaken wf X isdecl).
      move/onArity : X0 => /andP[] /andP[] /= Hind _ _.
      unshelve eapply declared_inductive_to_gen in isdecl; eauto.
      eapply wf_universes_inst; eauto.
      exact (weaken_lookup_on_global_env' Σ.1 _ _ wf (proj1 isdecl)).
      now eapply consistent_instance_ext_wf.

    - apply/andP; split; to_wfu.
      { eapply consistent_instance_ext_wf; eauto. }
      pose proof (declared_constructor_inv wf_universes_weaken wf X isdecl) as [sc [nthe onc]].
      unfold type_of_constructor.
      rewrite wf_universes_subst.
      { apply wf_universes_inds.
        now eapply consistent_instance_ext_wf. }
      move/on_ctype : onc => /andP[] /andP[] /= onc _ _.
      clear nthe. unshelve eapply declared_constructor_to_gen in isdecl; eauto.
      eapply wf_universes_inst; eauto.
      exact (weaken_lookup_on_global_env' Σ.1 _ _ wf (proj1 (proj1 isdecl))).
      now eapply consistent_instance_ext_wf.

    - rewrite wf_universes_mkApps in H6.
      move/andP: H6 => /= [] wfu; rewrite forallb_app.
      move/andP=> [] wfpars wfinds.
      rewrite /wf_universes /on_universes in wfu.
      rewrite wfu wfpars wf_universes_mkApps /=
        forallb_app wfinds /= H0 /= !andb_true_r.
      pose proof (declared_inductive_inv wf_universes_weaken wf X isdecl).
      move:(onArity X3) => /andP[] /andP[] /= hty _ _.
      rewrite (ind_arity_eq X3) in hty.
      rewrite !wf_universes_it_mkProd_or_LetIn in hty.
      move/and3P: hty => [] wfp wfindis wfisort.
      have ond : on_udecl_prop Σ (ind_universes mdecl).
      { eapply (weaken_lookup_on_global_env' _ _ (InductiveDecl mdecl)); eauto.
      unshelve eapply declared_inductive_to_gen in isdecl; eauto.
      }
      eapply wf_ctx_universes_inner in wfp => //.
      eapply wf_ctx_universes_inner in wfindis => //.
      rtoProp; repeat split.
      * cbn in H8. to_wfu.
        eapply isSortRel_wf_relevance; tea.
      * erewrite wf_ctx_inner_compare_decls; tea.
        erewrite wf_ctx_inner_lengths.
        1: apply wf_ctx_inner_ind_predicate_context; eauto.
        + cbn -[wf_qualityb] in wfisort. to_wfu.
          eapply wf_relevance_closed.
          eapply isSortRel_wf_relevance; tea.
          apply X3.
        + apply (consistent_instance_quals_length H2).
        + apply (consistent_instance_univs_length H2).
      * have wfbrctx : All (fun cdecl => wf_ctx_inner (polymorphic_instance (ind_universes mdecl)) (cstr_args cdecl)) (ind_ctors idecl).
        { pose proof (onConstructors := onConstructors X3).
          clear -wf ond onConstructors.
          red in onConstructors. solve_all. destruct X.
          move : on_ctype => /andP[] /andP[] /= wfty _ _.
          rewrite cstr_eq in wfty.
          rewrite !wf_universes_it_mkProd_or_LetIn in wfty.
          move/and3P: wfty => [] _ clargs _.
          apply wf_ctx_universes_inner in clargs => //. }
        solve_all.
        erewrite wf_ctx_inner_compare_decls; [|tea].
        erewrite wf_ctx_inner_lengths.
        1:apply wf_ctx_inner_cstr_branch_context; tas.
        + apply (consistent_instance_quals_length H2).
        + apply (consistent_instance_univs_length H2).
      * rewrite wf_universes_it_mkLambda_or_LetIn H7 andb_true_r.
        move: H4.
        rewrite /wf_ctx_universes forallb_app => /andP[hctx _] //.

    - rewrite /subst1. rewrite wf_universes_subst.
      constructor => //. eapply All_rev.
      rewrite wf_universes_mkApps in H2.
      move/andP: H2 => [].
      now intros _ hargs%forallb_All.
      pose proof (declared_projection_inv wf_universes_weaken wf X isdecl).
      destruct (declared_inductive_inv); simpl in *.
      destruct ind_ctors as [|cs []] => //.
      destruct ind_cunivs as [|cunivs []] => //;
      destruct X0 as [[[? ?] ?] ?] => //.
      red in o0.
      destruct nth_error eqn:heq => //.
      destruct o0  as [_ ->].
      rewrite wf_universes_mkApps {1}/wf_universes /= -!/(wf_universes _ _) in H2.
      move/andP: H2 => [wfu wfargs].
      move/on_instance_reflect: wfu => wfu.
      unshelve eapply declared_projection_to_gen in isdecl; eauto.
      eapply (wf_universes_inst (ind_universes mdecl)); eauto.
      exact (weaken_lookup_on_global_env' Σ.1 _ _ wf (proj1 (proj1 (proj1 isdecl)))).
      rewrite wf_universes_subst.
      eapply wf_universes_inds; eauto.
      eapply wf_abstract_instance.
      rewrite wf_universes_subst. apply wf_projs.
      rewrite wf_universes_lift.
      rewrite smash_context_app smash_context_acc in heq.
      autorewrite with len in heq. rewrite nth_error_app_lt in heq.
      autorewrite with len. lia.
      rewrite nth_error_subst_context in heq.
      autorewrite with len in heq. simpl in heq.
      epose proof (nth_error_lift_context_eq _ (smash_context [] (ind_params mdecl)) _ _).
      autorewrite with len in H0. simpl in H0. rewrite -> H0 in heq. clear H0.
      autorewrite with len in heq.
      simpl in heq.
      destruct nth_error eqn:hnth; simpl in * => //.
      noconf heq. simpl.
      rewrite wf_universes_subst.
      apply wf_extended_subst.
      rewrite ind_arity_eq in onArity. move:onArity => /andP[] /andP[] /= Hs _ _.
      rewrite !wf_universes_it_mkProd_or_LetIn in Hs.
      now move/andP: Hs => /andP /andP [].
      rewrite wf_universes_lift.
      eapply wf_universes_local_ctx_smash in s.
      eapply wf_universes_local_ctx_nth_error in s; eauto.

    - clear X X1. unfold on_def_type, on_def_body in *; cbn in *.
      apply/andP; split; auto.
      solve_all.
      eapply nth_error_all in X0 as ((? & _)%andb_and & _)%andb_and; eauto.

    - clear X X1. unfold on_def_type, on_def_body in *; cbn in *.
      apply/andP; split; auto.
      solve_all.
      eapply nth_error_all in X0 as ((? & _)%andb_and & _)%andb_and; eauto.

    - apply/andP; split; eauto.
      destruct X0; cbn => //.
      rtoProp; intuition eauto. solve_all.
      destruct X0; cbn => //.
      simp prim_type. cbn. rtoProp; intuition.
Qed.

  Lemma typing_wf_universes {Σ : global_env_ext} {Γ t T} :
    wf Σ ->
    Σ ;;; Γ |- t : T -> wf_universes Σ t && wf_universes Σ T.
  Proof using Type.
    intros wfΣ Hty.
    exact (env_prop_typing wf_types _ wfΣ _ _ _ Hty).
  Qed.

  Lemma typing_wf_ctx_universes {Σ : global_env_ext} {Γ} :
    wf Σ ->
    wf_local Σ Γ ->
    wf_ctx_universes Σ Γ.
  Proof using Type.
    intros wfΣ Hty.
    by apply (env_prop_wf_local wf_types).
  Qed.

  Lemma typing_wf_sort {Σ : global_env_ext} {Γ t s} :
    wf Σ ->
    Σ ;;; Γ |- t : tSort s -> wf_sort Σ s.
  Proof using Type.
    intros wfΣ Hty.
    apply typing_wf_universes in Hty as [_ wfs]%andb_and; auto.
    cbn -[wf_qualityb] in wfs. rewrite -/(wf_sortb _ s) in wfs. now to_wfu.
  Qed.

  Lemma isType_wf_universes {Σ Γ T} : wf Σ.1 -> isType Σ Γ T -> wf_universes Σ T.
  Proof using Type.
    intros wfΣ (_ & s & Hs & _). now eapply typing_wf_universes in Hs as [HT _]%andb_and.
  Qed.
End CheckerFlags.

Arguments wf_universe_reflect {Σ u}.
#[global] Hint Resolve wf_sort_type1 wf_sort_super wf_sort_sup wf_sort_product : pcuic.

#[global]
Hint Extern 4 (wf_sort _ ?u) =>
  match goal with
  [ H : typing _ _ _ (tSort u) |- _ ] => apply (typing_wf_sort _ H)
  end : pcuic.



From Stdlib Require Import Morphisms.
From Stdlib Require Import ssreflect.
Set SimplIsCbn.

Section SubstIdentity.
  Context `{cf:checker_flags}.

  Lemma subst_instance_level_abs l n Σ qs :
    wf Σ ->
    LevelSet.In l (LevelSet.union
     (fold_right LevelSet.add LevelSet.empty
        (unfold n Level.lvar)) (global_levels Σ)) ->
    subst_instance_level (Instance.make qs (unfold n Level.lvar)) l = l.
  Proof using Type.
    intros wfΣ lin.
    eapply LevelSet.union_spec in lin.
    destruct lin.
    - apply LevelSet_In_fold_right_add in H.
      destruct l; simpl; auto.
      eapply In_unfold_inj in H; [|congruence].
      pose proof (proj1 (nth_error_unfold Level.lvar n n0) H).
      now rewrite (nth_error_nth _ _ _ H0).
    - eapply not_var_global_levels in wfΣ.
      specialize (wfΣ l H). simpl in wfΣ.
      destruct l => //.
  Qed.

  Lemma consistent_instance_ext_abstract_instance Σ udecl :
    wf Σ ->
    wf_global_ext Σ udecl ->
    consistent_instance_ext (Σ, udecl) udecl (abstract_instance udecl).
  Proof using Type.
    intros wfΣ wf_glob_ext.
    red. red.
    destruct udecl as [|[univs cst]] eqn:indu.
    { simpl; split; reflexivity. }
    repeat split.
    - simpl abstract_instance. eapply forallb_mapi => //.
      intros i Hi. unfold global_ext_qualities.
      apply QualitySet.mem_spec, QualitySet.union_spec. left.
      unfold qualities_of_udecl. simpl.
      rewrite (mapi_unfold Quality.var). eapply QualitySet_In_fold_right_add.
      induction #|qualities univs| in i, Hi |- *; try lia.
      simpl. eapply in_or_app. destruct (eq_dec i n).
      * subst. right; simpl; auto.
      * left; apply IHn; lia.
    - now rewrite mapi_length.
    - simpl abstract_instance.
      eapply forallb_mapi => //.
      intros i Hi. unfold global_ext_levels.
      apply LevelSet.mem_spec, LevelSet.union_spec. left.
      unfold levels_of_udecl. simpl.
      rewrite (mapi_unfold Level.lvar).
      eapply LevelSet_In_fold_right_add.
      induction #|Universes.universes univs| in i, Hi |- *; try lia.
      simpl. eapply in_or_app. destruct (eq_dec i n).
      * subst. right; simpl; auto.
      * left; apply IHn; lia.
    - now rewrite mapi_length.
    - simpl. rewrite (mapi_unfold Level.lvar).
      assert(CS.Equal (subst_instance_cstrs (Instance.make (mapi (fun (i : nat) (_ : name) => Quality.var i) (qualities univs)) (unfold #|Universes.universes univs| Level.lvar)) cst) cst).
      { unfold CS.Equal; intros a.
        unfold subst_instance_cstrs.
        red in wf_glob_ext.
        destruct wf_glob_ext as [_ wfext].
        unfold on_udecl_prop in wfext.
        simpl constraints_of_udecl in wfext.
        simpl levels_of_udecl in wfext.
        rewrite (mapi_unfold Level.lvar) in wfext.
        clear indu.
        simpl fst in wfext.
        revert wfext.
        eapply ConstraintSetProp.fold_rec_weak; auto.
        2:reflexivity.
        * intros s s' a' eqs H.
          intros Hf.
          rewrite <- eqs in Hf. rewrite -eqs; auto.
        * intros x a0 s nin equiv.
          intros cadd.
          eapply CS_For_all_add in cadd as [cadd Ps].
          specialize (equiv Ps). clear Ps.
          destruct x as [[l c] r]. destruct cadd as [inl inr].
          unfold subst_instance_cstr. simpl.
          eapply subst_instance_level_abs with (qs := (mapi (fun (i : nat) (_ : name) => Quality.var i) (qualities univs))) in inl; auto.
          eapply subst_instance_level_abs with (qs := (mapi (fun (i : nat) (_ : name) => Quality.var i) (qualities univs))) in inr; auto.
          rewrite inl inr.
          rewrite !CS.add_spec.
          intuition auto. }
      unfold valid_constraints. destruct check_univs; auto.
      unfold valid_constraints0, satisfies. intros v.
      destruct univs. cbn in *. rewrite H.
      eapply CS_For_all_union.
  Qed.

  Lemma global_level_subst_abs Σ u :
    wf_ext_wk Σ ->
    LevelSet.In u (global_ext_levels Σ) ->
    subst_instance_level (abstract_instance Σ.2) u = u.
  Proof using Type.
    intros [wfΣ onu] declu.
    destruct u; simpl; auto. cbn -[global_ext_levels] in declu.
    eapply in_var_global_ext in declu; auto.
    destruct (udecl_prop_in_var_poly declu) as [[univs csts] eq].
    rewrite eq in declu |- *. simpl in *.
    rewrite mapi_unfold in declu |- *.
    eapply LevelSet_In_fold_right_add in declu.
    eapply In_unfold_inj in declu; try congruence.
    eapply (nth_error_unfold Level.lvar) in declu.
    now rewrite (nth_error_nth _ _ _ declu).
  Qed.

  Lemma wf_qvar_subst_abs Σ qv :
    wf_qvar Σ qv ->
    subst_instance_qvar (abstract_instance Σ.2) qv = Quality.qVar qv.
  Proof using Type.
    intros declq.
    cbn -[global_ext_qualities] in declq.
    destruct qv.
    eapply in_var_global_ext' in declq; auto.
    destruct (udecl_in_var_quality_poly declq) as [[univs csts] eq].
    rewrite eq in declq |- *. simpl in *.
    rewrite mapi_unfold in declq |- *.
    eapply QualitySet_In_fold_right_add in declq.
    eapply In_unfold_inj in declq.
    2: intros ?? H; injection H => //.
    eapply (nth_error_unfold Quality.var) in declq.
    now rewrite (nth_error_nth _ _ _ declq).
  Qed.

  Lemma wf_quality_subst_abs Σ q :
    wf_quality Σ q ->
    subst_instance_quality (abstract_instance Σ.2) q = q.
  Proof using Type.
    intros declq.
    destruct q; simpl; auto.
    apply wf_qvar_subst_abs; auto.
  Qed.
(*
  Lemma consistent_instance_ext_subst_abs Σ decl u :
    wf_ext_wk Σ ->
    consistent_instance_ext Σ decl u ->
    subst_instance (abstract_instance Σ.2) u = u.
  Proof using Type.
    intros wfΣ cu.
    destruct decl.
    { simpl in cu. destruct u, cu; simpl in *.
      apply length_nil in H, H0. rewrite H H0 //. }
    destruct u as [qs us].
    rewrite /subst_instance /subst_instance_instance // /Instance.make /=.
    destruct cu as (hq & _ & hl & _).
    cbn -[QualitySet.mem LS.mem] in *.
    apply forallb_All in hq, hl.
    f_equal; eapply All_map_id, All_impl; eauto; cbn -[QualitySet.mem LS.mem]; intros.
    - eapply wf_quality_subst_abs; tea.
      now apply QualitySet.mem_spec.
    - eapply global_level_subst_abs; tea.
      now apply LS.mem_spec.
  Qed. *)

  Lemma wf_instance_subst_abs Σ u :
    wf_ext_wk Σ ->
    wf_instance Σ u ->
    subst_instance (abstract_instance Σ.2) u = u.
  Proof using Type.
    intros wfΣ cu.
    destruct u as [qs us].
    rewrite /subst_instance /subst_instance_instance // /Instance.make /=.
    destruct cu; cbn in *.
    f_equal; solve_all.
    - by apply wf_quality_subst_abs.
    - by apply global_level_subst_abs.
  Qed.

  Lemma in_global_ext_subst_abs_level Σ l :
    wf_ext_wk Σ ->
    LevelSet.In (LevelExpr.get_level l) (global_ext_levels Σ) ->
    subst_instance (abstract_instance Σ.2) l = l.
  Proof using Type.
    intros wfΣ cu.
    destruct l; auto.
    apply global_level_subst_abs in cu; tea.
    cbn in cu.
    destruct t; cbn; auto.
    rewrite /= nth_nth_error in cu.
    destruct nth_error => //. congruence.
  Qed.

  Lemma wf_universe_subst_abs Σ u :
    wf_ext_wk Σ ->
    wf_universe Σ u ->
    subst_instance_universe (abstract_instance Σ.2) u = u.
  Proof using Type.
    intros wf cu.
    simpl in cu.
    apply NonEmptySetFacts.eq_univ'.
    intros l.
    rewrite In_subst_instance.
    split.
    - intros [x [inx ->]].
      specialize (cu _ inx).
      unfold subst_instance.
      apply in_global_ext_subst_abs_level in cu; eauto.
      unfold subst_instance in cu. now rewrite cu.
    - intros inl.
      specialize (cu _ inl). exists l; split; auto.
      now rewrite in_global_ext_subst_abs_level.
  Qed.

  Lemma wf_sort_subst_abs Σ u :
    wf_ext_wk Σ ->
    wf_sort Σ u ->
    subst_instance_sort (abstract_instance Σ.2) u = u.
  Proof using Type.
    intros wf cu.
    destruct u; simpl; auto.
    - f_equal.
      by apply wf_universe_subst_abs.
    - destruct cu as [hq hl].
      eapply wf_qvar_subst_abs in hq as ->; tea.
      eapply wf_universe_subst_abs in hl; tea.
      rewrite /subst_instance hl //.
  Qed.

  (* Lemma consistent_instance_ext_subst_abs_inds Σ decl ind u bodies :
    wf_ext_wk Σ ->
    consistent_instance_ext Σ decl u ->
    subst_instance (abstract_instance Σ.2) (inds ind u bodies) =
      (inds ind u bodies).
  Proof using Type.
    intros wf cu.
    unfold inds. generalize #|bodies|.
    induction n; simpl; auto. rewrite IHn; f_equal.
    now rewrite [subst_instance_instance _ _](consistent_instance_ext_subst_abs _ _ _ wf cu).
  Qed. *)

  Lemma wf_relevance_subst_abs Σ r :
    wf_ext_wk Σ ->
    wf_relevance Σ r ->
    subst_instance (abstract_instance Σ.2) r = r.
  Proof using Type.
    intros wf cu.
    unfold subst_instance, subst_instance_aname, subst_instance_binder_annot.
    destruct r => //=. cbn in cu.
    rewrite wf_qvar_subst_abs //.
  Qed.

  Lemma wf_relevance_subst_abs_aname Σ na :
    wf_ext_wk Σ ->
    wf_relevance Σ na.(binder_relevance) ->
    subst_instance (abstract_instance Σ.2) na = na.
  Proof using Type.
    intros wf cu.
    unfold subst_instance, subst_instance_aname, subst_instance_binder_annot.
    destruct na as [n r]; f_equal; cbn in *.
    by apply wf_relevance_subst_abs.
  Qed.

  Lemma app_inj {A} (l l' l0 l0' : list A) :
    #|l| = #|l0| ->
    l ++ l' = l0 ++ l0' ->
    l = l0 /\ l' = l0'.
  Proof using Type.
    induction l in l', l0, l0' |- *; destruct l0; simpl in * => //; auto.
    intros [= eq] [= -> eql].
    now destruct (IHl _ _ _ eq eql).
  Qed.

  Ltac to_wfu :=
    repeat match goal with
    | [ H: is_true (wf_qualityb _ ?x) |- _ ] => apply (elimT (@wf_qualityP _ x)) in H
    | [ |- is_true (wf_qualityb _ ?x) ] => apply (introT (@wf_qualityP _ x))
    | [ H: is_true (wf_universeb _ ?x) |- _ ] => apply (elimT (@wf_universe_reflect _ x)) in H
    | [ |- is_true (wf_universeb _ ?x) ] => apply (introT (@wf_universe_reflect _ x))
    | [ H: is_true (Sort.on_sort _ (wf_universeb _) _ _ ?x) |- _ ] => apply (elimT (@wf_sort_reflect _ x)) in H
    | [ |- is_true (Sort.on_sort _ (wf_universeb _) _ _ ?x) ] => apply (introT (@wf_sort_reflect _ x))
    | [ H: is_true (wf_sortb _ ?x) |- _ ] => apply (elimT (@wf_sort_reflect _ x)) in H
    | [ |- is_true (wf_sortb _ ?x) ] => apply (introT (@wf_sort_reflect _ x))
    | [ H: is_true (on_instance (wf_qualityb _) (wf_universeb _) ?x) |- _ ] => apply (elimT (@on_instance_reflect _ x)) in H
    | [ |- is_true (on_instance (wf_qualityb _) (wf_universeb _) ?x) ] => apply (introT (@on_instance_reflect _ x))
    | [ H: is_true (on_relevance _ _ ?x) |- _ ] => apply (elimT (@on_relevance_reflect _ x)) in H
    | [ |- is_true (on_relevance _ _ ?x) ] => apply (introT (@on_relevance_reflect _ x))
    | [ H: is_true (on_binder_annot _ ?x) |- _ ] => apply (elimT (@on_binder_annot_reflect _ x)) in H
    | [ |- is_true (on_binder_annot _ ?x) ] => apply (introT (@on_binder_annot_reflect _ x))
    end.

  Lemma subst_abstract_instance_id Σ t :
    wf_ext_wk Σ ->
    wf_universes Σ t ->
    let u := abstract_instance (snd Σ) in
    t@[u] = t.
  Proof.
    intros wfΣ h.
    induction t in h |- * using term_forall_list_ind.
    all: cbn -[Universe.make' wf_qualityb] in *; auto.
    all: rtoProp; to_wfu.
    all: try solve [ f_equal; solve_all; to_wfu; eauto using wf_relevance_subst_abs_aname, wf_instance_subst_abs, wf_sort_subst_abs ].
    - f_equal; auto.
      + unfold map_case_info.
        destruct ci; cbn; f_equal.
        destruct ci_relevance => //.
        by apply wf_relevance_subst_abs.
      + unfold map_predicate.
        destruct p; cbn in *; f_equal; solve_all.
        by apply wf_instance_subst_abs.
      + solve_all.
    - f_equal.
      destruct p as [? []]; cbnr.
      cbn -[Universe.make'] in X, h. do 2 f_equal.
      unfold mapu_array_model.
      rtoProp. to_wfu. destruct X as (?&?&?).
      destruct a; cbn -[Universe.make'] in *; f_equal; eauto.
      + apply global_level_subst_abs; tas.
        by apply wf_universe_make.
      + solve_all.
  Qed.

  Lemma subst_context_abstract_instance_id Σ Γ :
    wf_ext_wk Σ ->
    wf_ctx_universes Σ Γ ->
    let u := abstract_instance (snd Σ) in
    Γ@[u] = Γ.
  Proof.
    unfold subst_instance, subst_instance_context, map_context_gen, map_decl_gen, wf_ctx_universes.
    solve_all.
    move: H => /andP[]/andP[] hna hb hty.
    destruct x; cbn -[wf_qualityb] in *; f_equal.
    - to_wfu.
      by apply wf_relevance_subst_abs_aname.
    - destruct decl_body; cbnr. f_equal.
      by apply subst_abstract_instance_id.
    - by apply subst_abstract_instance_id.
  Qed.

(*
  Lemma subst_abstract_instance_id :
    env_prop (fun Σ Γ t T =>
        wf_ext_wk Σ ->
        let u := abstract_instance (snd Σ) in
        subst_instance u t = t × subst_instance u T = T)
        (fun Σ _ j => wf_ext_wk Σ ->
        let u := abstract_instance (snd Σ) in
        lift_wfu_term (fun t => subst_instance u t = t) (fun u => wf_sort Σ u) j)
        (fun Σ Γ =>
        wf_ext_wk Σ ->
        let u := abstract_instance (snd Σ) in
        subst_instance u Γ = Γ).
  Proof using Type.

    eapply typing_ind_env; intros; simpl in *; auto.
    { apply lift_typing_subjtyp with (1 := X). 2: intros s Hs; now depelim Hs.
      intros ?? []; auto. }

    { apply All_local_env_cst in X0. clear -X0 X1.
      eapply All2_eq, All2_map_left. apply All_All2 with (1 := X0) => decl IH.
      destruct IH as (? & ? & ?), decl as [na bo ty]; tas; unfold map_decl; cbn in *.
      f_equal; tas. destruct bo => //. all: admit. cbn in *. now f_equal. }

    all: try ((subst u || subst u0); split; [f_equal|]; intuition eauto).

    1:{ rewrite subst_instance_lift. f_equal.
      generalize H. rewrite -H1 /subst_instance /= nth_error_map H /= => [=].
      intros Hdecl. now rewrite -{2}Hdecl. }

    all: try match goal with H : lift_wfu_term _ _ _ |- _ => destruct H as (Htm & Hty & Hs); cbn in Htm, Hty, Hs end.
    all:try (solve [f_equal; eauto; try congruence]).
    all:try (rewrite ?subst_instance_two; f_equal; eapply consistent_instance_ext_subst_abs; eauto).

    - now rewrite wf_sort_subst_abs.

    - rewrite wf_sort_subst_abs //.
      now apply wf_sort_super.

    - rewrite product_subst_instance. do 2 f_equal; tas.
      now noconf b0.

    - intuition auto. noconf a; noconf b; noconf b0.
      rewrite subst_instance_subst /= /subst1.
      repeat (f_equal; simpl; auto).

    - rewrite /type_of_constructor subst_instance_subst subst_instance_two.
      erewrite consistent_instance_ext_subst_abs; eauto. f_equal.
      eapply consistent_instance_ext_subst_abs_inds; eauto.

    - solve_all; simpl in *.
      * rewrite subst_instance_mkApps /= /subst_instance /= in b0.
        eapply mkApps_nApp_inj in b0 as [Hi Hpars] => //.
        now noconf Hi.
      * rewrite subst_instance_mkApps /= /subst_instance /= in b0.
        eapply mkApps_nApp_inj in b0 as [Hi Hpars] => //.
        rewrite map_app in Hpars.
        eapply app_inj in Hpars as [Hpars hinds]. 2:now len.
        rewrite -{2}(map_id (pparams p)) in Hpars.
        now apply map_eq_inj in Hpars.

    - solve_all.

    - rewrite subst_instance_mkApps. f_equal.
      * rewrite /ptm.
        rewrite subst_instance_it_mkLambda_or_LetIn.
        rewrite subst_instance_app in H.
        eapply app_inj in H as []; [|now len].
        rewrite H. now f_equal.
      * rewrite map_app.
        rewrite subst_instance_mkApps /= /subst_instance /= in b0.
        eapply mkApps_nApp_inj in b0 as [Hi Hpars] => //.
        rewrite map_app in Hpars.
        eapply app_inj in Hpars as [Hpars hinds]. 2:now len.
        now rewrite hinds /= a0.
    - rewrite subst_instance_subst /=.
      rewrite /subst_instance /=.
      rewrite subst_instance_mkApps in b.
      eapply mkApps_nApp_inj in b as [Hi Hpars] => //.
      f_equal.
      * rewrite a; f_equal.
        rewrite /subst_instance_list. now rewrite map_rev Hpars.
      * rewrite [subst_instance_constr _ _]subst_instance_two.
        noconf Hi. now rewrite [subst_instance _ u]H.
    - solve_all.
      + destruct a0 as (_ & X & _); tas.
      + destruct b as (X & _); tas.
    - eapply nth_error_all in X0 as (_ & X0 & _); tea.
    - solve_all.
      + destruct a0 as (_ & X & _); tas.
      + destruct b as (X & _); tas.
    - eapply nth_error_all in X0 as (_ & X0 & _); tea.
    - destruct p as [? []]; cbnr. do 2 f_equal.
      depelim X0. specialize (hty X1); specialize (hdef X1).
      unfold mapu_array_model; destruct a; cbn -[Universe.make'] in *.
      f_equal; intuition eauto.
      * rewrite /subst_instance subst_instance_universe_make in b.
        now injection b as e.
      * solve_all.
    - depelim X0; cbn => //=. depelim X. simp prim_type. cbn. f_equal; intuition eauto.
      do 2 f_equal.
      cbn -[Universe.make'] in b.
      rewrite /subst_instance subst_instance_universe_make in b.
      injection b as e. unfold subst_instance_instance. cbn; f_equal.
      now unfold subst_instance in e.
  Qed. *)

  Lemma typed_subst_abstract_instance Σ Γ t T :
    wf_ext_wk Σ ->
    Σ ;;; Γ |- t : T ->
    let u := abstract_instance Σ.2 in
    subst_instance u t = t.
  Proof using Type.
    intros wfΣ H.
    apply subst_abstract_instance_id; tas.
    apply typing_wf_universes in H as (?&?)%andb_and; tas.
    apply wfΣ.
  Qed.

  Lemma subst_instance_id Σ Γ :
    wf_ext_wk Σ ->
    wf_local Σ Γ ->
    let u := abstract_instance Σ.2 in
    subst_instance u Γ = Γ.
  Proof using Type.
    intros wfΣ H.
    eapply subst_context_abstract_instance_id; tas.
    apply typing_wf_ctx_universes; tas.
    apply wfΣ.
  Qed.

End SubstIdentity.

Hint Resolve declared_inductive_wf_ext_wk declared_inductive_wf_global_ext : pcuic.
