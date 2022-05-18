signature MRBNF_FP_DEF_SUGAR =
sig
  val co_datatypes: BNF_Util.fp_kind -> (mixfix list -> binding list -> binding list ->
      binding list -> binding list list -> binding list -> (string * sort) list ->
      typ list * typ list list -> BNF_Def.bnf list -> BNF_Comp.absT_info list -> local_theory ->
      BNF_FP_Util.fp_result * local_theory) ->
    Ctr_Sugar.ctr_options
    * ((((((binding option * (typ * sort)) list * binding) * mixfix)
         * ((binding, binding * typ) Ctr_Sugar.ctr_spec * mixfix) list) *
         (binding * binding * binding))
       * term list) list ->
    local_theory -> local_theory
end;

structure MRBNF_FP_Def_Sugar : MRBNF_FP_DEF_SUGAR =
struct

(*open Ctr_Sugar
open BNF_FP_Rec_Sugar_Util
open BNF_Util
open BNF_Comp
open BNF_Def
open BNF_FP_Util
open BNF_FP_Def_Sugar_Tactics*)

fun define_co_datatypes prepare_plugins prepare_constraint prepare_typ prepare_term fp construct_fp
    ((raw_plugins, discs_sels0), specs) lthy =
  let
    val plugins = prepare_plugins lthy raw_plugins;
    val discs_sels = discs_sels0 orelse fp = Greatest_FP;

    val nn = length specs;
    val fp_bs = map type_binding_of_spec specs;
    val fp_b_names = map Binding.name_of fp_bs;
    val fp_common_name = mk_common_name fp_b_names;
    val map_bs = map map_binding_of_spec specs;
    val rel_bs = map rel_binding_of_spec specs;
    val pred_bs = map pred_binding_of_spec specs;

    fun prepare_type_arg (_, (ty, c)) =
      let val TFree (s, _) = prepare_typ lthy ty in
        TFree (s, prepare_constraint lthy c)
      end;

    val Ass0 = map (map prepare_type_arg o type_args_named_constrained_of_spec) specs;
    val unsorted_Ass0 = map (map (resort_tfree_or_tvar \<^sort>\<open>type\<close>)) Ass0;
    val unsorted_As = Library.foldr1 (merge_type_args fp) unsorted_Ass0;
    val num_As = length unsorted_As;

    val set_boss = map (map fst o type_args_named_constrained_of_spec) specs;
    val set_bss = map (map (the_default Binding.empty)) set_boss;

    fun add_fake_type spec =
      Typedecl.basic_typedecl {final = true}
        (type_binding_of_spec spec, num_As, Mixfix.reset_pos (mixfix_of_spec spec));

    val (fake_T_names, fake_lthy) = fold_map add_fake_type specs lthy;

    val qsoty = quote o Syntax.string_of_typ fake_lthy;

    val _ = (case Library.duplicates (op =) unsorted_As of [] => ()
      | A :: _ => error ("Duplicate type parameter " ^ qsoty A ^ " in " ^ co_prefix fp ^
          "datatype specification"));

    val bad_args =
      map (Logic.type_map (singleton (Variable.polymorphic lthy))) unsorted_As
      |> filter_out Term.is_TVar;
    val _ = null bad_args orelse
      error ("Locally fixed type argument " ^ qsoty (hd bad_args) ^ " in " ^ co_prefix fp ^
        "datatype specification");

    val mixfixes = map mixfix_of_spec specs;

    val _ = (case Library.duplicates Binding.eq_name fp_bs of [] => ()
      | b :: _ => error ("Duplicate type name declaration " ^ quote (Binding.name_of b)));

    val mx_ctr_specss = map mixfixed_ctr_specs_of_spec specs;
    val ctr_specss = map (map fst) mx_ctr_specss;
    val ctr_mixfixess = map (map snd) mx_ctr_specss;

    val disc_bindingss = map (map disc_of_ctr_spec) ctr_specss;
    val ctr_bindingss =
      map2 (fn fp_b_name => map (Binding.qualify false fp_b_name o ctr_of_ctr_spec)) fp_b_names
        ctr_specss;
    val ctr_argsss = map (map args_of_ctr_spec) ctr_specss;

    val sel_bindingsss = map (map (map fst)) ctr_argsss;
    val fake_ctr_Tsss0 = map (map (map (prepare_typ fake_lthy o snd))) ctr_argsss;
    val raw_sel_default_eqss = map sel_default_eqs_of_spec specs;

    val (As :: _) :: fake_ctr_Tsss =
      burrow (burrow (Syntax.check_typs fake_lthy)) (Ass0 :: fake_ctr_Tsss0);
    val As' = map dest_TFree As;

    val rhs_As' = fold (fold (fold Term.add_tfreesT)) fake_ctr_Tsss [];
    val _ = (case subtract (op =) As' rhs_As' of [] => ()
      | extras => error ("Extra type variables on right-hand side: " ^
          commas (map (qsoty o TFree) extras)));

    val fake_Ts = map (fn s => Type (s, As)) fake_T_names;

    val ((((Bs0, Cs), Es), Xs), _) = lthy
      |> fold (Variable.declare_typ o resort_tfree_or_tvar dummyS) unsorted_As
      |> mk_TFrees num_As
      ||>> mk_TFrees nn
      ||>> mk_TFrees nn
      ||>> variant_tfrees fp_b_names;

    fun eq_fpT_check (T as Type (s, Ts)) (T' as Type (s', Ts')) =
        s = s' andalso (Ts = Ts' orelse
          error ("Wrong type arguments in " ^ co_prefix fp ^ "recursive type " ^ qsoty T ^
            " (expected " ^ qsoty T' ^ ")"))
      | eq_fpT_check _ _ = false;

    fun freeze_fp (T as Type (s, Ts)) =
        (case find_index (eq_fpT_check T) fake_Ts of
          ~1 => Type (s, map freeze_fp Ts)
        | kk => nth Xs kk)
      | freeze_fp T = T;

    val unfreeze_fp = Term.typ_subst_atomic (Xs ~~ fake_Ts);

    val ctrXs_Tsss = map (map (map freeze_fp)) fake_ctr_Tsss;
    val ctrXs_repTs = map mk_sumprodT_balanced ctrXs_Tsss;

    val _ =
      let
        fun add_deps i =
          fold (fn T => fold_index (fn (j, X) =>
            (i <> j andalso exists_subtype_in [X] T) ? insert (op =) (i, j)) Xs);

        val add_missing_nodes = fold (AList.default (op =) o rpair []) (0 upto nn - 1);

        val deps = fold_index (uncurry (fold o add_deps)) ctrXs_Tsss []
          |> AList.group (op =)
          |> add_missing_nodes;

        val G = Int_Graph.make (map (apfst (rpair ())) deps);
        val sccs = map (sort int_ord) (Int_Graph.strong_conn G);

        val str_of_scc = prefix (co_prefix fp ^ "datatype ") o
          space_implode " and " o map (suffix " = \<dots>" o Long_Name.base_name);

        fun warn [_] = ()
          | warn sccs =
            warning ("Defined types not fully mutually " ^ co_prefix fp ^ "recursive\n\
              \Alternative specification:\n" ^
              cat_lines (map (prefix "  " o str_of_scc o map (nth fp_b_names)) sccs));
      in
        warn (order_strong_conn (op =) Int_Graph.make Int_Graph.topological_order deps sccs)
      end;

    val killed_As =
      map_filter (fn (A, set_bos) => if exists is_none set_bos then SOME A else NONE)
        (As ~~ transpose set_boss);

    val (((pre_bnfs, absT_infos), _), (fp_res as {bnfs = fp_bnfs as any_fp_bnf :: _, ctors = ctors0,
             dtors = dtors0, xtor_co_recs = xtor_co_recs0, xtor_co_induct, dtor_ctors, ctor_dtors,
             ctor_injects, dtor_injects, xtor_maps, xtor_setss, xtor_rels, xtor_co_rec_thms,
             xtor_rel_co_induct, dtor_set_inducts, xtor_co_rec_transfers, xtor_co_rec_o_maps, ...},
           lthy)) =
      fixpoint_bnf false I (construct_fp mixfixes map_bs rel_bs pred_bs set_bss) fp_bs
        (map dest_TFree As) (map dest_TFree killed_As) (map dest_TFree Xs) ctrXs_repTs
        empty_comp_cache lthy
      handle BAD_DEAD (X, X_backdrop) =>
        (case X_backdrop of
          Type (bad_tc, _) =>
          let
            val fake_T = qsoty (unfreeze_fp X);
            val fake_T_backdrop = qsoty (unfreeze_fp X_backdrop);
            fun register_hint () =
              "\nUse the " ^ quote (#1 \<^command_keyword>\<open>bnf\<close>) ^ " command to register " ^
              quote bad_tc ^ " as a bounded natural functor to allow nested (co)recursion through \
              \it";
          in
            if is_some (bnf_of lthy bad_tc) orelse is_some (fp_sugar_of lthy bad_tc) then
              error ("Inadmissible " ^ co_prefix fp ^ "recursive occurrence of type " ^ fake_T ^
                " in type expression " ^ fake_T_backdrop)
            else if is_some (Old_Datatype_Data.get_info (Proof_Context.theory_of lthy)
                bad_tc) then
              error ("Unsupported " ^ co_prefix fp ^ "recursive occurrence of type " ^ fake_T ^
                " via the old-style datatype " ^ quote bad_tc ^ " in type expression " ^
                fake_T_backdrop ^ register_hint ())
            else
              error ("Unsupported " ^ co_prefix fp ^ "recursive occurrence of type " ^ fake_T ^
                " via type constructor " ^ quote bad_tc ^ " in type expression " ^ fake_T_backdrop ^
                register_hint ())
          end);

    val time = time lthy;
    val timer = time (Timer.startRealTimer ());

    val fp_nesting_bnfs = nesting_bnfs lthy ctrXs_Tsss Xs;
    val live_nesting_bnfs = nesting_bnfs lthy ctrXs_Tsss As;

    val pre_map_defs = map map_def_of_bnf pre_bnfs;
    val pre_set_defss = map set_defs_of_bnf pre_bnfs;
    val pre_rel_defs = map rel_def_of_bnf pre_bnfs;
    val fp_nesting_set_maps = maps set_map_of_bnf fp_nesting_bnfs;
    val fp_nesting_rel_eq_onps = map rel_eq_onp_of_bnf fp_nesting_bnfs;
    val live_nesting_map_id0s = map map_id0_of_bnf live_nesting_bnfs;
    val live_nesting_map_ident0s = map map_ident0_of_bnf live_nesting_bnfs;
    val live_nesting_set_maps = maps set_map_of_bnf live_nesting_bnfs;
    val live_nesting_rel_eqs = map rel_eq_of_bnf live_nesting_bnfs;
    val live_nesting_rel_eq_onps = map rel_eq_onp_of_bnf live_nesting_bnfs;

    val liveness = liveness_of_fp_bnf num_As any_fp_bnf;
    val live = live_of_bnf any_fp_bnf;
    val _ =
      if live = 0 andalso exists (not o Binding.is_empty) (map_bs @ rel_bs @ pred_bs) then
        warning "Map function, relator, and predicator names ignored"
      else
        ();

    val Bs = @{map 3} (fn alive => fn A as TFree (_, S) => fn B =>
        if alive then resort_tfree_or_tvar S B else A)
      liveness As Bs0;

    val B_ify_T = Term.typ_subst_atomic (As ~~ Bs);
    val B_ify = Term.map_types B_ify_T;

    val live_AsBs = filter (op <>) (As ~~ Bs);

    val abss = map #abs absT_infos;
    val reps = map #rep absT_infos;
    val absTs = map #absT absT_infos;
    val repTs = map #repT absT_infos;
    val abs_injects = map #abs_inject absT_infos;
    val abs_inverses = map #abs_inverse absT_infos;
    val type_definitions = map #type_definition absT_infos;

    val ctors = map (mk_ctor As) ctors0;
    val dtors = map (mk_dtor As) dtors0;

    val fpTs = map (domain_type o fastype_of) dtors;
    val fpBTs = map B_ify_T fpTs;

    val real_unfreeze_fp = Term.typ_subst_atomic (Xs ~~ fpTs);

    val ctr_Tsss = map (map (map real_unfreeze_fp)) ctrXs_Tsss;
    val ns = map length ctr_Tsss;
    val kss = map (fn n => 1 upto n) ns;
    val mss = map (map length) ctr_Tsss;

    val (xtor_co_recs, recs_args_types, corecs_args_types) =
      mk_co_recs_prelims lthy fp ctr_Tsss fpTs Cs absTs repTs ns mss xtor_co_recs0;

    fun define_ctrs_dtrs_for_type_etc fp_bnf fp_b fpT C E ctor dtor xtor_co_rec ctor_dtor dtor_ctor
        ctor_inject pre_map_def pre_set_defs pre_rel_def fp_map_thm fp_set_thms fp_rel_thm n ks ms
        abs abs_inject type_definition ctr_bindings ctr_mixfixes ctr_Tss disc_bindings sel_bindingss
        raw_sel_default_eqs lthy =
      let
        val fp_b_name = Binding.name_of fp_b;

        val ((xss, ctrs0, ctor_iff_dtor_thm, ctr_defs), lthy) =
          define_ctrs_dtrs_for_type fp_b_name fpT ctor dtor ctor_dtor dtor_ctor n ks abs
            ctr_bindings ctr_mixfixes ctr_Tss lthy;

        val ctrs = map (mk_ctr As) ctrs0;

        val sel_default_eqs =
          let
            val sel_Tss = map (map (curry (op -->) fpT)) ctr_Tss;
            val sel_bTs =
              flat sel_bindingss ~~ flat sel_Tss
              |> filter_out (Binding.is_empty o fst)
              |> distinct (Binding.eq_name o apply2 fst);
            val sel_default_lthy = fake_local_theory_for_sel_defaults sel_bTs lthy
          in
            map (prepare_term sel_default_lthy) raw_sel_default_eqs
          end;

        fun mk_binding pre =
          Binding.qualify false fp_b_name (Binding.prefix_name (pre ^ "_") fp_b);

        fun massage_res (ctr_sugar, maps_sets_rels) =
          (maps_sets_rels, (ctrs, xss, ctor_iff_dtor_thm, ctr_defs, ctr_sugar));
      in
        (wrap_ctrs plugins fp discs_sels fp_b_name ctor_inject n ms abs_inject type_definition
           disc_bindings sel_bindingss sel_default_eqs ctrs0 ctor_iff_dtor_thm ctr_defs
         #> (fn (ctr_sugar, lthy) =>
           derive_map_set_rel_pred_thms plugins fp live As Bs C E abs_inverses ctr_defs
             fp_nesting_set_maps fp_nesting_rel_eq_onps live_nesting_map_id0s live_nesting_set_maps
             live_nesting_rel_eqs live_nesting_rel_eq_onps [] fp_b_name fp_bnf fp_bnfs fpT ctor
             ctor_dtor dtor_ctor pre_map_def pre_set_defs pre_rel_def fp_map_thm fp_set_thms
             fp_rel_thm [] [] [] ctr_Tss ctr_sugar lthy
           |>> pair ctr_sugar)
         ##>>
           (if fp = Least_FP then define_rec (the recs_args_types) mk_binding fpTs Cs reps
            else define_corec (the corecs_args_types) mk_binding fpTs Cs abss) xtor_co_rec
         #>> apfst massage_res, lthy)
      end;

    fun wrap_ctrs_derive_map_set_rel_pred_thms_define_co_rec_for_types (wrap_one_etcs, lthy) =
      fold_map I wrap_one_etcs lthy
      |>> apsnd split_list o apfst (apsnd @{split_list 5} o apfst @{split_list 17} o split_list)
        o split_list;

    fun mk_simp_thms ({injects, distincts, case_thms, ...} : ctr_sugar) co_recs map_thms rel_injects
        rel_distincts set_thmss =
      injects @ distincts @ case_thms @ co_recs @ map_thms @ rel_injects @ rel_distincts @
      set_thmss;

    fun mk_co_rec_transfer_goals lthy co_recs =
      let
        val BE_ify = Term.subst_atomic_types (live_AsBs @ (Cs ~~ Es));

        val ((Rs, Ss), names_lthy) = lthy
          |> mk_Frees "R" (map (uncurry mk_pred2T) live_AsBs)
          ||>> mk_Frees "S" (map2 mk_pred2T Cs Es);

        val co_recBs = map BE_ify co_recs;
      in
        (Rs, Ss, map2 (mk_parametricity_goal lthy (Rs @ Ss)) co_recs co_recBs, names_lthy)
      end;

    fun derive_rec_transfer_thms lthy recs rec_defs (SOME (_, _, _, xsssss)) =
      let
        val (Rs, Ss, goals, _) = mk_co_rec_transfer_goals lthy recs;
        val goal = Logic.mk_conjunction_balanced goals;
        val vars = Variable.add_free_names lthy goal [];
      in
        Goal.prove_sorry lthy vars [] goal
          (fn {context = ctxt, prems = _} =>
             mk_rec_transfer_tac ctxt nn ns (map (Thm.cterm_of ctxt) Ss)
               (map (Thm.cterm_of ctxt) Rs) xsssss rec_defs xtor_co_rec_transfers pre_rel_defs
               live_nesting_rel_eqs)
        |> Thm.close_derivation \<^here>
        |> Conjunction.elim_balanced nn
      end;

    fun derive_rec_o_map_thmss lthy recs rec_defs =
      if live = 0 then
        replicate nn []
      else
        let
          fun variant_names n pre = fst (Variable.variant_fixes (replicate n pre) lthy);

          val maps0 = map map_of_bnf fp_bnfs;
          val f_names = variant_names num_As "f";
          val fs = map2 (curry Free) f_names (map (op -->) (As ~~ Bs));
          val live_gs = AList.find (op =) (fs ~~ liveness) true;

          val gmaps = map (fn map0 => Term.list_comb (mk_map live As Bs map0, live_gs)) maps0;

          val rec_arg_Ts = binder_fun_types (hd (map fastype_of recs));

          val num_rec_args = length rec_arg_Ts;
          val g_Ts = map B_ify_T rec_arg_Ts;
          val g_names = variant_names num_rec_args "g";
          val gs = map2 (curry Free) g_names g_Ts;
          val grecs = map (fn recx => Term.list_comb (Term.map_types B_ify_T recx, gs)) recs;

          val rec_o_map_lhss = map2 (curry HOLogic.mk_comp) grecs gmaps;

          val ABfs = (As ~~ Bs) ~~ fs;

          fun mk_rec_arg_arg (x as Free (_, T)) =
            let val U = B_ify_T T in
              if T = U then x else build_map lthy [] [] (the o AList.lookup (op =) ABfs) (T, U) $ x
            end;

          fun mk_rec_o_map_arg rec_arg_T h =
            let
              val x_Ts = binder_types rec_arg_T;
              val m = length x_Ts;
              val x_names = variant_names m "x";
              val xs = map2 (curry Free) x_names x_Ts;
              val xs' = map mk_rec_arg_arg xs;
            in
              fold_rev Term.lambda xs (Term.list_comb (h, xs'))
            end;

          fun mk_rec_o_map_rhs recx =
            let val args = map2 mk_rec_o_map_arg rec_arg_Ts gs in
              Term.list_comb (recx, args)
            end;

          val rec_o_map_rhss = map mk_rec_o_map_rhs recs;

          val rec_o_map_goals =
            map2 (fold_rev (fold_rev Logic.all) [fs, gs] o HOLogic.mk_Trueprop oo
              curry HOLogic.mk_eq) rec_o_map_lhss rec_o_map_rhss;
          val rec_o_map_thms =
            @{map 3} (fn goal => fn rec_def => fn ctor_rec_o_map =>
                Goal.prove_sorry lthy [] [] goal (fn {context = ctxt, ...} =>
                  mk_co_rec_o_map_tac ctxt rec_def pre_map_defs live_nesting_map_ident0s
                    abs_inverses ctor_rec_o_map)
                |> Thm.close_derivation \<^here>)
              rec_o_map_goals rec_defs xtor_co_rec_o_maps;
        in
          map single rec_o_map_thms
        end;

    fun derive_note_induct_recs_thms_for_types
        ((((map_thmss, map_disc_iffss, map_selsss, rel_injectss, rel_distinctss, rel_selss,
            rel_intross, rel_casess, pred_injectss, set_thmss, set_selsssss, set_introsssss,
            set_casess, ctr_transferss, case_transferss, disc_transferss, sel_transferss),
           (ctrss, _, ctor_iff_dtors, ctr_defss, ctr_sugars)),
          (recs, rec_defs)), lthy) =
      let
        val ((induct_thms, induct_thm, induct_attrs), (rec_thmss, rec_attrs)) =
          derive_induct_recs_thms_for_types plugins pre_bnfs recs_args_types xtor_co_induct
            xtor_co_rec_thms live_nesting_bnfs fp_nesting_bnfs fpTs Cs Xs ctrXs_Tsss abs_inverses
            type_definitions abs_inverses ctrss ctr_defss recs rec_defs lthy;

        val rec_transfer_thmss =
          map single (derive_rec_transfer_thms lthy recs rec_defs recs_args_types);

        val induct_type_attr = Attrib.internal o K o Induct.induct_type;
        val induct_pred_attr = Attrib.internal o K o Induct.induct_pred;

        val ((rel_induct_thmss, common_rel_induct_thms),
             (rel_induct_attrs, common_rel_induct_attrs)) =
          if live = 0 then
            ((replicate nn [], []), ([], []))
          else
            let
              val ((rel_induct_thms, common_rel_induct_thm), rel_induct_attrs) =
                derive_rel_induct_thms_for_types lthy nn fpTs As Bs ctrss ctr_Tsss
                  (map #exhaust ctr_sugars) xtor_rel_co_induct ctr_defss ctor_injects
                  pre_rel_defs abs_inverses live_nesting_rel_eqs;
            in
              ((map single rel_induct_thms, single common_rel_induct_thm),
               (rel_induct_attrs, rel_induct_attrs))
            end;

        val rec_o_map_thmss = derive_rec_o_map_thmss lthy recs rec_defs;

        val simp_thmss =
          @{map 6} mk_simp_thms ctr_sugars rec_thmss map_thmss rel_injectss rel_distinctss
            set_thmss;

        val common_notes =
          (if nn > 1 then
             [(inductN, [induct_thm], K induct_attrs),
              (rel_inductN, common_rel_induct_thms, K common_rel_induct_attrs)]
           else
             [])
          |> massage_simple_notes fp_common_name;

        val notes =
          [(inductN, map single induct_thms, fn T_name => induct_attrs @ [induct_type_attr T_name]),
           (recN, rec_thmss, K rec_attrs),
           (rec_o_mapN, rec_o_map_thmss, K []),
           (rec_transferN, rec_transfer_thmss, K []),
           (rel_inductN, rel_induct_thmss, K (rel_induct_attrs @ [induct_pred_attr ""])),
           (simpsN, simp_thmss, K [])]
          |> massage_multi_notes fp_b_names fpTs;
      in
        lthy
        |> Spec_Rules.add Binding.empty Spec_Rules.equational recs (flat rec_thmss)
        |> plugins code_plugin ? Code.declare_default_eqns (map (rpair true) (flat rec_thmss))
        |> Local_Theory.notes (common_notes @ notes)
        (* for "datatype_realizer.ML": *)
        |>> name_noted_thms
          (fst (dest_Type (hd fpTs)) ^ implode (map (prefix "_") (tl fp_b_names))) inductN
        |-> interpret_bnfs_register_fp_sugars plugins fpTs fpBTs Xs Least_FP pre_bnfs absT_infos
          fp_nesting_bnfs live_nesting_bnfs fp_res ctrXs_Tsss ctor_iff_dtors ctr_defss ctr_sugars
          recs rec_defs map_thmss [induct_thm] (map single induct_thms) rec_thmss (replicate nn [])
          (replicate nn []) rel_injectss rel_distinctss map_disc_iffss map_selsss rel_selss
          rel_intross rel_casess pred_injectss set_thmss set_selsssss set_introsssss set_casess
          ctr_transferss case_transferss disc_transferss sel_transferss (replicate nn [])
          (replicate nn []) rec_transfer_thmss common_rel_induct_thms rel_induct_thmss []
          (replicate nn []) rec_o_map_thmss
      end;

    fun derive_corec_transfer_thms lthy corecs corec_defs =
      let
        val (Rs, Ss, goals, _) = mk_co_rec_transfer_goals lthy corecs;
        val (_, _, _, (((pgss, pss, qssss, gssss), _), _)) = the corecs_args_types;
        val goal = Logic.mk_conjunction_balanced goals;
        val vars = Variable.add_free_names lthy goal [];
      in
        Goal.prove_sorry lthy vars [] goal
          (fn {context = ctxt, prems = _} =>
             mk_corec_transfer_tac ctxt (map (Thm.cterm_of ctxt) Ss) (map (Thm.cterm_of ctxt) Rs)
               type_definitions corec_defs xtor_co_rec_transfers pre_rel_defs
               live_nesting_rel_eqs (flat pgss) pss qssss gssss)
        |> Thm.close_derivation \<^here>
        |> Conjunction.elim_balanced (length goals)
      end;

    fun derive_map_o_corec_thmss lthy0 lthy2 corecs corec_defs =
      if live = 0 then
        replicate nn []
      else
        let
          fun variant_names n pre = fst (Variable.variant_fixes (replicate n pre) lthy0);

          val maps0 = map map_of_bnf fp_bnfs;
          val f_names = variant_names num_As "f";
          val fs = map2 (curry Free) f_names (map (op -->) (As ~~ Bs));
          val live_fs = AList.find (op =) (fs ~~ liveness) true;

          val fmaps = map (fn map0 => Term.list_comb (mk_map live As Bs map0, live_fs)) maps0;

          val corec_arg_Ts = binder_fun_types (hd (map fastype_of corecs));

          val num_rec_args = length corec_arg_Ts;
          val g_names = variant_names num_rec_args "g";
          val gs = map2 (curry Free) g_names corec_arg_Ts;
          val gcorecs = map (fn corecx => Term.list_comb (corecx, gs)) corecs;

          val map_o_corec_lhss = map2 (curry HOLogic.mk_comp) fmaps gcorecs;

          val ABfs = (As ~~ Bs) ~~ fs;

          fun mk_map_o_corec_arg corec_argB_T g =
            let
              val T = range_type (fastype_of g);
              val U = range_type corec_argB_T;
            in
              if T = U then
                g
              else
                HOLogic.mk_comp (build_map lthy2 [] [] (the o AList.lookup (op =) ABfs) (T, U), g)
            end;

          fun mk_map_o_corec_rhs corecx =
            let val args = map2 (mk_map_o_corec_arg o B_ify_T) corec_arg_Ts gs in
              Term.list_comb (B_ify corecx, args)
            end;

          val map_o_corec_rhss = map mk_map_o_corec_rhs corecs;

          val map_o_corec_goals =
            map2 (fold_rev (fold_rev Logic.all) [fs, gs] o HOLogic.mk_Trueprop oo
              curry HOLogic.mk_eq) map_o_corec_lhss map_o_corec_rhss;

          val map_o_corec_thms =
            @{map 3} (fn goal => fn corec_def => fn dtor_map_o_corec =>
                Goal.prove_sorry lthy2 [] [] goal (fn {context = ctxt, ...} =>
                  mk_co_rec_o_map_tac ctxt corec_def pre_map_defs live_nesting_map_ident0s
                    abs_inverses dtor_map_o_corec)
                |> Thm.close_derivation \<^here>)
              map_o_corec_goals corec_defs xtor_co_rec_o_maps;
        in
          map single map_o_corec_thms
        end;

    fun derive_note_coinduct_corecs_thms_for_types
        ((((map_thmss, map_disc_iffss, map_selsss, rel_injectss, rel_distinctss, rel_selss,
            rel_intross, rel_casess, pred_injectss, set_thmss, set_selsssss, set_introsssss,
            set_casess, ctr_transferss, case_transferss, disc_transferss, sel_transferss),
           (_, _, ctor_iff_dtors, ctr_defss, ctr_sugars)),
          (corecs, corec_defs)), lthy) =
      let
        val (([(coinduct_thms, coinduct_thm), (coinduct_strong_thms, coinduct_strong_thm)],
              (coinduct_attrs, common_coinduct_attrs)),
             corec_thmss, corec_disc_thmss,
             (corec_disc_iff_thmss, corec_disc_iff_attrs), (corec_sel_thmsss, corec_sel_attrs)) =
          derive_coinduct_corecs_thms_for_types lthy pre_bnfs (the corecs_args_types) xtor_co_induct
            dtor_injects dtor_ctors xtor_co_rec_thms live_nesting_bnfs fpTs Cs Xs ctrXs_Tsss kss mss
            ns abs_inverses abs_inverses I ctr_defss ctr_sugars corecs corec_defs;

        fun distinct_prems ctxt thm =
          Goal.prove (*no sorry*) ctxt [] []
            (thm |> Thm.prop_of |> Logic.strip_horn |>> distinct (op aconv) |> Logic.list_implies)
            (fn _ => HEADGOAL (cut_tac thm THEN' assume_tac ctxt) THEN ALLGOALS eq_assume_tac);

        fun eq_ifIN _ [thm] = thm
          | eq_ifIN ctxt (thm :: thms) =
              distinct_prems ctxt (@{thm eq_ifI} OF
                (map (unfold_thms ctxt @{thms atomize_imp[of _ "t = u" for t u]})
                  [thm, eq_ifIN ctxt thms]));

        val corec_code_thms = map (eq_ifIN lthy) corec_thmss;
        val corec_sel_thmss = map flat corec_sel_thmsss;

        val coinduct_type_attr = Attrib.internal o K o Induct.coinduct_type;
        val coinduct_pred_attr = Attrib.internal o K o Induct.coinduct_pred;

        val flat_corec_thms = append oo append;

        val corec_transfer_thmss = map single (derive_corec_transfer_thms lthy corecs corec_defs);

        val ((rel_coinduct_thmss, common_rel_coinduct_thms),
             (rel_coinduct_attrs, common_rel_coinduct_attrs)) =
          if live = 0 then
            ((replicate nn [], []), ([], []))
          else
            let
              val ((rel_coinduct_thms, common_rel_coinduct_thm),
                   (rel_coinduct_attrs, common_rel_coinduct_attrs)) =
                derive_rel_coinduct_thms_for_types lthy nn fpTs ns As Bs mss ctr_sugars abs_inverses
                  abs_injects ctor_injects dtor_ctors pre_rel_defs ctr_defss xtor_rel_co_induct
                  live_nesting_rel_eqs;
            in
              ((map single rel_coinduct_thms, single common_rel_coinduct_thm),
               (rel_coinduct_attrs, common_rel_coinduct_attrs))
            end;

        val map_o_corec_thmss = derive_map_o_corec_thmss lthy lthy corecs corec_defs;

        val (set_induct_thms, set_induct_attrss) =
          derive_set_induct_thms_for_types lthy nn fpTs (map #ctrs ctr_sugars)
            (map (map (mk_set As)) (map sets_of_bnf fp_bnfs)) dtor_set_inducts
            (map #exhaust ctr_sugars) (flat pre_set_defss) (flat ctr_defss) dtor_ctors abs_inverses
          |> split_list;

        val simp_thmss =
          @{map 6} mk_simp_thms ctr_sugars
            (@{map 3} flat_corec_thms corec_disc_thmss corec_disc_iff_thmss corec_sel_thmss)
            map_thmss rel_injectss rel_distinctss set_thmss;

        val common_notes =
          (set_inductN, set_induct_thms, nth set_induct_attrss) ::
          (if nn > 1 then
            [(coinductN, [coinduct_thm], K common_coinduct_attrs),
             (coinduct_strongN, [coinduct_strong_thm], K common_coinduct_attrs),
             (rel_coinductN, common_rel_coinduct_thms, K common_rel_coinduct_attrs)]
           else [])
          |> massage_simple_notes fp_common_name;

        val notes =
          [(coinductN, map single coinduct_thms,
            fn T_name => coinduct_attrs @ [coinduct_type_attr T_name]),
           (coinduct_strongN, map single coinduct_strong_thms, K coinduct_attrs),
           (corecN, corec_thmss, K []),
           (corec_codeN, map single corec_code_thms, K (nitpicksimp_attrs)),
           (corec_discN, corec_disc_thmss, K []),
           (corec_disc_iffN, corec_disc_iff_thmss, K corec_disc_iff_attrs),
           (corec_selN, corec_sel_thmss, K corec_sel_attrs),
           (corec_transferN, corec_transfer_thmss, K []),
           (map_o_corecN, map_o_corec_thmss, K []),
           (rel_coinductN, rel_coinduct_thmss, K (rel_coinduct_attrs @ [coinduct_pred_attr ""])),
           (simpsN, simp_thmss, K [])]
          |> massage_multi_notes fp_b_names fpTs;
      in
        lthy
        |> fold (Spec_Rules.add Binding.empty Spec_Rules.equational corecs)
          [flat corec_sel_thmss, flat corec_thmss]
        |> plugins code_plugin ? Code.declare_default_eqns (map (rpair true) corec_code_thms)
        |> Local_Theory.notes (common_notes @ notes)
        |-> interpret_bnfs_register_fp_sugars plugins fpTs fpBTs Xs Greatest_FP pre_bnfs absT_infos
          fp_nesting_bnfs live_nesting_bnfs fp_res ctrXs_Tsss ctor_iff_dtors ctr_defss ctr_sugars
          corecs corec_defs map_thmss [coinduct_thm, coinduct_strong_thm]
          (transpose [coinduct_thms, coinduct_strong_thms]) corec_thmss corec_disc_thmss
          corec_sel_thmsss rel_injectss rel_distinctss map_disc_iffss map_selsss rel_selss
          rel_intross rel_casess pred_injectss set_thmss set_selsssss set_introsssss set_casess
          ctr_transferss case_transferss disc_transferss sel_transferss corec_disc_iff_thmss
          (map single corec_code_thms) corec_transfer_thmss common_rel_coinduct_thms
          rel_coinduct_thmss set_induct_thms (replicate nn (if nn = 1 then set_induct_thms else []))
          map_o_corec_thmss
      end;

    val lthy = lthy
      |> live > 0 ? fold2 (fn Type (s, _) => fn bnf => register_bnf_raw s bnf) fpTs fp_bnfs
      |> @{fold_map 29} define_ctrs_dtrs_for_type_etc fp_bnfs fp_bs fpTs Cs Es ctors dtors
        xtor_co_recs ctor_dtors dtor_ctors ctor_injects pre_map_defs pre_set_defss pre_rel_defs
        xtor_maps xtor_setss xtor_rels ns kss mss abss abs_injects type_definitions ctr_bindingss
        ctr_mixfixess ctr_Tsss disc_bindingss sel_bindingsss raw_sel_default_eqss
      |> wrap_ctrs_derive_map_set_rel_pred_thms_define_co_rec_for_types
      |> case_fp fp derive_note_induct_recs_thms_for_types
        derive_note_coinduct_corecs_thms_for_types;

    val timer = time (timer ("Constructors, discriminators, selectors, etc., for the new " ^
      co_prefix fp ^ "datatype"));
  in
    lthy
  end;

fun co_datatypes fp = define_co_datatypes (K I) (K I) (K I) (K I) fp;

end;