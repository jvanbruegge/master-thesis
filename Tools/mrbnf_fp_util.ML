signature MRBNF_FP_UTIL =
sig
  type fp_result =
    {Ts: typ list,
     mrbnfs: MRBNF_Def.mrbnf list,
     pre_mrbnfs: MRBNF_Def.mrbnf list,
     absT_infos: MRBNF_Comp.absT_info list,
     ctors: term list,
     dtors: term list,
     xtor_un_folds: term list,
     xtor_co_recs: term list,
     xtor_co_induct: thm,
     dtor_ctors: thm list,
     ctor_dtors: thm list,
     ctor_injects: thm list,
     dtor_injects: thm list,
     xtor_maps: thm list,
     xtor_map_unique: thm,
     xtor_setss: thm list list,
     xtor_rels: thm list,
     xtor_un_fold_thms: thm list,
     xtor_co_rec_thms: thm list,
     xtor_un_fold_unique: thm,
     xtor_co_rec_unique: thm,
     xtor_un_fold_o_maps: thm list,
     xtor_co_rec_o_maps: thm list,
     xtor_un_fold_transfers: thm list,
     xtor_co_rec_transfers: thm list,
     xtor_rel_co_induct: thm,
     dtor_set_inducts: thm list}

  val morph_fp_result: morphism -> fp_result -> fp_result

  val fixpoint_mrbnf: bool -> (binding -> binding) ->
      (binding list -> (string * sort) list -> typ list * typ list list -> MRBNF_Def.mrbnf list ->
      MRBNF_Comp.absT_info list -> local_theory -> 'a) ->
    binding list -> (string * sort) list -> (string * sort) list -> (string * sort) list ->
    typ list -> ((string * sort) * MRBNF_Def.var_type) list list -> MRBNF_Comp.comp_cache -> local_theory ->
    ((MRBNF_Def.mrbnf list * MRBNF_Comp.absT_info list) * MRBNF_Comp.comp_cache) * 'a

  val derive_xtor_co_recs: MRBNF_Util.fp_kind -> binding list -> (typ list -> typ list) ->
    (typ list list * typ list) -> MRBNF_Def.mrbnf list -> term list -> term list ->
    thm -> thm list -> thm list -> thm list -> thm list ->
    (MRBNF_Comp.absT_info * MRBNF_Comp.absT_info) option list ->
    local_theory ->
    (term list * (thm list * thm * thm list * thm list)) * local_theory
end;

structure MRBNF_FP_Util : MRBNF_FP_UTIL =
struct

open BNF_FP_Util
open MRBNF_Def
open MRBNF_Comp
open BNF_FP_Rec_Sugar_Util
open BNF_Util
open BNF_FP_Util_Tactics

val preN = "pre_"

type fp_result =
  {Ts: typ list,
   mrbnfs: MRBNF_Def.mrbnf list,
   pre_mrbnfs: MRBNF_Def.mrbnf list,
   absT_infos: MRBNF_Comp.absT_info list,
   ctors: term list,
   dtors: term list,
   xtor_un_folds: term list,
   xtor_co_recs: term list,
   xtor_co_induct: thm,
   dtor_ctors: thm list,
   ctor_dtors: thm list,
   ctor_injects: thm list,
   dtor_injects: thm list,
   xtor_maps: thm list,
   xtor_map_unique: thm,
   xtor_setss: thm list list,
   xtor_rels: thm list,
   xtor_un_fold_thms: thm list,
   xtor_co_rec_thms: thm list,
   xtor_un_fold_unique: thm,
   xtor_co_rec_unique: thm,
   xtor_un_fold_o_maps: thm list,
   xtor_co_rec_o_maps: thm list,
   xtor_un_fold_transfers: thm list,
   xtor_co_rec_transfers: thm list,
   xtor_rel_co_induct: thm,
   dtor_set_inducts: thm list};

fun morph_fp_result phi {Ts, mrbnfs, pre_mrbnfs, absT_infos, ctors, dtors, xtor_un_folds,
    xtor_co_recs, xtor_co_induct, dtor_ctors, ctor_dtors, ctor_injects, dtor_injects, xtor_maps,
    xtor_map_unique, xtor_setss, xtor_rels, xtor_un_fold_thms, xtor_co_rec_thms,
    xtor_un_fold_unique, xtor_co_rec_unique, xtor_un_fold_o_maps,
    xtor_co_rec_o_maps, xtor_un_fold_transfers, xtor_co_rec_transfers, xtor_rel_co_induct,
    dtor_set_inducts} =
  {Ts = map (Morphism.typ phi) Ts,
   mrbnfs = map (morph_mrbnf phi) mrbnfs,
   pre_mrbnfs = map (morph_mrbnf phi) pre_mrbnfs,
   absT_infos = map (morph_absT_info phi) absT_infos,
   ctors = map (Morphism.term phi) ctors,
   dtors = map (Morphism.term phi) dtors,
   xtor_un_folds = map (Morphism.term phi) xtor_un_folds,
   xtor_co_recs = map (Morphism.term phi) xtor_co_recs,
   xtor_co_induct = Morphism.thm phi xtor_co_induct,
   dtor_ctors = map (Morphism.thm phi) dtor_ctors,
   ctor_dtors = map (Morphism.thm phi) ctor_dtors,
   ctor_injects = map (Morphism.thm phi) ctor_injects,
   dtor_injects = map (Morphism.thm phi) dtor_injects,
   xtor_maps = map (Morphism.thm phi) xtor_maps,
   xtor_map_unique = Morphism.thm phi xtor_map_unique,
   xtor_setss = map (map (Morphism.thm phi)) xtor_setss,
   xtor_rels = map (Morphism.thm phi) xtor_rels,
   xtor_un_fold_thms = map (Morphism.thm phi) xtor_un_fold_thms,
   xtor_co_rec_thms = map (Morphism.thm phi) xtor_co_rec_thms,
   xtor_un_fold_unique = Morphism.thm phi xtor_un_fold_unique,
   xtor_co_rec_unique = Morphism.thm phi xtor_co_rec_unique,
   xtor_un_fold_o_maps = map (Morphism.thm phi) xtor_un_fold_o_maps,
   xtor_co_rec_o_maps = map (Morphism.thm phi) xtor_co_rec_o_maps,
   xtor_un_fold_transfers = map (Morphism.thm phi) xtor_un_fold_transfers,
   xtor_co_rec_transfers = map (Morphism.thm phi) xtor_co_rec_transfers,
   xtor_rel_co_induct = Morphism.thm phi xtor_rel_co_induct,
   dtor_set_inducts = map (Morphism.thm phi) dtor_set_inducts};

fun absT_info_encodeT thy (SOME (src : absT_info, dst : absT_info)) src_absT =
    let
      val src_repT = mk_repT (#absT src) (#repT src) src_absT;
      val dst_absT = mk_absT thy (#repT dst) (#absT dst) src_repT;
    in
      dst_absT
    end
  | absT_info_encodeT _ NONE T = T;

fun absT_info_decodeT thy = absT_info_encodeT thy o Option.map swap;

fun absT_info_encode thy fp (opt as SOME (src : absT_info, dst : absT_info)) t =
    let
      val co_alg_funT = case_fp fp domain_type range_type;
      fun co_swap pair = case_fp fp I swap pair;
      val mk_co_comp = curry (HOLogic.mk_comp o co_swap);
      val mk_co_abs = case_fp fp mk_abs mk_rep;
      val mk_co_rep = case_fp fp mk_rep mk_abs;
      val co_abs = case_fp fp #abs #rep;
      val co_rep = case_fp fp #rep #abs;
      val src_absT = co_alg_funT (fastype_of t);
      val dst_absT = absT_info_encodeT thy opt src_absT;
      val co_src_abs = mk_co_abs src_absT (co_abs src);
      val co_dst_rep = mk_co_rep dst_absT (co_rep dst);
    in
      mk_co_comp (mk_co_comp t co_src_abs) co_dst_rep
    end
  | absT_info_encode _ _ NONE t = t;

fun absT_info_decode thy fp = absT_info_encode thy fp o Option.map swap;

fun mk_xtor_un_fold_xtor_thms ctxt fp un_folds xtors xtor_un_fold_unique map_id0s
    absT_info_opts =
  let
    val thy = Proof_Context.theory_of ctxt;
    fun mk_goal un_fold =
      let
        val rhs = list_comb (un_fold, @{map 2} (absT_info_encode thy fp) absT_info_opts xtors);
        val T = range_type (fastype_of rhs);
      in
        HOLogic.mk_eq (HOLogic.id_const T, rhs)
      end;
    val goal = HOLogic.mk_Trueprop (Library.foldr1 HOLogic.mk_conj (map mk_goal un_folds));
    fun mk_inverses NONE = []
      | mk_inverses (SOME (src, dst)) =
        [#type_definition dst RS @{thm type_definition.Abs_inverse[OF _ UNIV_I]},
         #type_definition src RS @{thm type_definition.Rep_inverse}];
    val inverses = maps mk_inverses absT_info_opts;
  in
    Goal.prove_sorry ctxt [] [] goal (fn {context = ctxt, prems = _} =>
      mk_xtor_un_fold_xtor_tac ctxt xtor_un_fold_unique map_id0s inverses)
    |> split_conj_thm |> map mk_sym
  end;

fun derive_xtor_co_recs fp bs mk_Ts (Dss, resDs) pre_mrbnfs xtors0 un_folds0
    xtor_un_fold_unique xtor_un_folds xtor_un_fold_transfers xtor_maps xtor_rels
    absT_info_opts lthy =
  let
    val thy = Proof_Context.theory_of lthy;
    fun co_swap pair = case_fp fp I swap pair;
    val mk_co_comp = curry (HOLogic.mk_comp o co_swap);
    fun mk_co_algT T U = case_fp fp (T --> U) (U --> T);
    val co_alg_funT = case_fp fp domain_type range_type;
    val mk_co_product = curry (case_fp fp mk_convol mk_case_sum);
    val co_proj1_const = case_fp fp fst_const (uncurry Inl_const o dest_sumT) o co_alg_funT;
    val co_proj2_const = case_fp fp snd_const (uncurry Inr_const o dest_sumT) o co_alg_funT;
    val mk_co_productT = curry (case_fp fp HOLogic.mk_prodT mk_sumT);
    val rewrite_comp_comp = case_fp fp @{thm rewriteL_comp_comp} @{thm rewriteR_comp_comp};

    val n = length pre_mrbnfs;
    val live = live_of_mrbnf (hd pre_mrbnfs);
    val bound = bound_of_mrbnf (hd pre_mrbnfs);
    val free = free_of_mrbnf (hd pre_mrbnfs);
    val m = live - n;
    val ks = 1 upto n;

    val map_id0s = map map_id0_of_mrbnf pre_mrbnfs;
    val map_comps = map map_comp_of_mrbnf pre_mrbnfs;
    val map_cong0s = map map_cong0_of_mrbnf pre_mrbnfs;
    val map_transfers = map map_transfer_of_mrbnf pre_mrbnfs;
    val sym_map_comp0s = map (mk_sym o map_comp0_of_mrbnf) pre_mrbnfs;

    val deads = fold (union (op =)) Dss resDs;
    val ((((((As, Bs), Xs), Ys), Bounds), Frees), names_lthy) = lthy
      |> fold Variable.declare_typ deads
      |> mk_TFrees m
      ||>> mk_TFrees m
      ||>> mk_TFrees n
      ||>> mk_TFrees n
      ||>> mk_TFrees bound
      ||>> mk_TFrees free;

    val XFTs = @{map 2} (fn Ds => mk_T_of_mrbnf Ds (As @ Xs) Bounds Frees) Dss pre_mrbnfs;
    val co_algXFTs = @{map 2} mk_co_algT XFTs Xs;
    val Ts = mk_Ts As;
    val un_foldTs = @{map 2} (fn T => fn X => co_algXFTs ---> mk_co_algT T X) Ts Xs;
    val un_folds = @{map 2} (force_typ names_lthy) un_foldTs un_folds0;
    val ABs = As ~~ Bs;
    val XYs = Xs ~~ Ys;

    val Us = map (typ_subst_atomic ABs) Ts;

    val TFTs = @{map 2} (fn Ds => mk_T_of_mrbnf Ds (As @ Ts) Bounds Frees) Dss pre_mrbnfs;

    val TFTs' = @{map 2} (absT_info_decodeT thy) absT_info_opts TFTs;
    val xtors = @{map 3} (force_typ names_lthy oo mk_co_algT) TFTs' Ts xtors0;

    val ids = map HOLogic.id_const As;
    val co_rec_Xs = @{map 2} mk_co_productT Ts Xs;
    val co_rec_Ys = @{map 2} mk_co_productT Us Ys;
    val co_rec_algXs = @{map 2} mk_co_algT co_rec_Xs Xs;
    val co_proj1s = map co_proj1_const co_rec_algXs;
    val co_rec_maps = @{map 2} (fn Ds =>
      mk_map_of_mrbnf Ds (As @ case_fp fp co_rec_Xs Ts) (As @ case_fp fp Ts co_rec_Xs) Bounds Frees) Dss pre_mrbnfs;
    val co_rec_Ts = @{map 2} (fn Ds => mk_T_of_mrbnf Ds (As @ co_rec_Xs) Bounds Frees) Dss pre_mrbnfs
    val co_rec_argTs = @{map 2} mk_co_algT co_rec_Ts Xs;
    val co_rec_resTs = @{map 2} mk_co_algT Ts Xs;

    val (((co_rec_ss, fs), xs), names_lthy) = names_lthy
      |> mk_Frees "s" co_rec_argTs
      ||>> mk_Frees "f" co_rec_resTs
      ||>> mk_Frees "x" (case_fp fp TFTs' Xs);

    val co_rec_strs =
      @{map 4} (fn xtor => fn s => fn mapx => fn absT_info_opt =>
        mk_co_product (mk_co_comp (absT_info_encode thy fp absT_info_opt xtor)
          (list_comb (mapx, ids @ co_proj1s))) s)
      xtors co_rec_ss co_rec_maps absT_info_opts;

    val theta = Xs ~~ co_rec_Xs;
    val co_rec_un_folds = map (subst_atomic_types theta) un_folds;

    val co_rec_spec0s = map (fn un_fold => list_comb (un_fold, co_rec_strs)) co_rec_un_folds;

    val co_rec_ids = @{map 2} (mk_co_comp o co_proj1_const) co_rec_algXs co_rec_spec0s;
    val co_rec_specs = @{map 2} (mk_co_comp o co_proj2_const) co_rec_algXs co_rec_spec0s;

    val co_recN = case_fp fp ctor_recN dtor_corecN;
    fun co_rec_bind i = nth bs (i - 1) |> Binding.prefix_name (co_recN ^ "_");
    val co_rec_def_bind = rpair [] o Binding.concealed o Thm.def_binding o co_rec_bind;

    fun co_rec_spec i =
      fold_rev (Term.absfree o Term.dest_Free) co_rec_ss (nth co_rec_specs (i - 1));

    val ((co_rec_frees, (_, co_rec_def_frees)), (lthy, lthy_old)) =
      lthy
      |> (snd o Local_Theory.begin_nested)
      |> fold_map (fn i =>
        Local_Theory.define ((co_rec_bind i, NoSyn), (co_rec_def_bind i, co_rec_spec i))) ks
      |>> apsnd split_list o split_list
      ||> `Local_Theory.end_nested;

    val phi = Proof_Context.export_morphism lthy_old lthy;
    val co_rec_names = map (fst o dest_Const o Morphism.term phi) co_rec_frees;
    val co_recs = @{map 2} (fn name => fn resT =>
      Const (name, co_rec_argTs ---> resT)) co_rec_names co_rec_resTs;
    val co_rec_defs = map (fn def =>
      mk_unabs_def n (HOLogic.mk_obj_eq (Morphism.thm phi def))) co_rec_def_frees;

    val xtor_un_fold_xtor_thms =
      mk_xtor_un_fold_xtor_thms lthy fp (map (Term.subst_atomic_types (Xs ~~ Ts)) un_folds)
        xtors xtor_un_fold_unique map_id0s absT_info_opts;

    val co_rec_id_thms =
      let
        val goal = @{map 2} (fn T => fn t => HOLogic.mk_eq (t, HOLogic.id_const T)) Ts co_rec_ids
          |> Library.foldr1 HOLogic.mk_conj |> HOLogic.mk_Trueprop;
        val vars = Variable.add_free_names lthy goal [];
      in
        Goal.prove_sorry lthy vars [] goal
          (fn {context = ctxt, prems = _} => mk_xtor_co_rec_id_tac ctxt xtor_un_fold_xtor_thms
            xtor_un_fold_unique xtor_un_folds map_comps)
        |> Thm.close_derivation \<^here>
        |> split_conj_thm
      end;

    val co_rec_app_ss = map (fn co_rec => list_comb (co_rec, co_rec_ss)) co_recs;
    val co_products = @{map 2} (fn T => mk_co_product (HOLogic.id_const T)) Ts co_rec_app_ss;
    val co_rec_maps_rev = @{map 2} (fn Ds =>
      mk_map_of_mrbnf Ds (As @ case_fp fp Ts co_rec_Xs) (As @ case_fp fp co_rec_Xs Ts) Bounds Frees) Dss pre_mrbnfs;
    fun mk_co_app f g x = case_fp fp (f $ (g $ x)) (g $ (f $ x));
    val co_rec_expand_thms = map (fn thm => thm RS
      case_fp fp @{thm convol_expand_snd} @{thm case_sum_expand_Inr_pointfree}) co_rec_id_thms;
    val xtor_co_rec_thms =
      let
        fun mk_goal co_rec s mapx xtor x absT_info_opt =
          let
            val lhs = mk_co_app co_rec xtor x;
            val rhs = mk_co_app s
              (list_comb (mapx, ids @ co_products) |> absT_info_decode thy fp absT_info_opt) x;
          in
            mk_Trueprop_eq (lhs, rhs)
          end;
        val goals =
          @{map 6} mk_goal co_rec_app_ss co_rec_ss co_rec_maps_rev xtors xs absT_info_opts;
      in
        map2 (fn goal => fn un_fold =>
          Variable.add_free_names lthy goal []
          |> (fn vars => Goal.prove_sorry lthy vars [] goal
            (fn {context = ctxt, prems = _} =>
              mk_xtor_co_rec_tac ctxt un_fold co_rec_defs co_rec_expand_thms))
          |> Thm.close_derivation \<^here>)
        goals xtor_un_folds
      end;

    val co_product_fs = @{map 2} (fn T => mk_co_product (HOLogic.id_const T)) Ts fs;
    val co_rec_expand'_thms = map (fn thm =>
      thm RS case_fp fp @{thm convol_expand_snd'} @{thm case_sum_expand_Inr'}) co_rec_id_thms;
    val xtor_co_rec_unique_thm =
      let
        fun mk_prem f s mapx xtor absT_info_opt =
          let
            val lhs = mk_co_comp f xtor;
            val rhs = mk_co_comp s (list_comb (mapx, ids @ co_product_fs))
              |> absT_info_decode thy fp absT_info_opt;
          in
            mk_Trueprop_eq (co_swap (lhs, rhs))
          end;
        val prems = @{map 5} mk_prem fs co_rec_ss co_rec_maps_rev xtors absT_info_opts;
        val concl = @{map 2} (curry HOLogic.mk_eq) fs co_rec_app_ss
          |> Library.foldr1 HOLogic.mk_conj |> HOLogic.mk_Trueprop;
        val goal = Logic.list_implies (prems, concl);
        val vars = Variable.add_free_names lthy goal [];
        fun mk_inverses NONE = []
          | mk_inverses (SOME (src, dst)) =
            [#type_definition dst RS @{thm type_copy_Rep_o_Abs} RS rewrite_comp_comp,
             #type_definition src RS @{thm type_copy_Abs_o_Rep}];
        val inverses = maps mk_inverses absT_info_opts;
      in
        Goal.prove_sorry lthy vars [] goal
          (fn {context = ctxt, prems = _} => mk_xtor_co_rec_unique_tac ctxt fp co_rec_defs
            co_rec_expand'_thms xtor_un_fold_unique map_id0s sym_map_comp0s inverses)
        |> Thm.close_derivation \<^here>
      end;

    val xtor_co_rec_o_map_thms = if forall is_none absT_info_opts
      then
        mk_xtor_co_iter_o_map_thms fp true m xtor_co_rec_unique_thm
          (map (mk_pointfree2 lthy) xtor_maps) (map (mk_pointfree2 lthy) xtor_co_rec_thms)
          sym_map_comp0s map_cong0s
      else
        replicate n refl (* FIXME *);

    val ABphiTs = @{map 2} mk_pred2T As Bs;
    val XYphiTs = @{map 2} mk_pred2T Xs Ys;

    val ((ABphis, XYphis), names_lthy) = names_lthy
      |> mk_Frees "R" ABphiTs
      ||>> mk_Frees "S" XYphiTs;

    val xtor_co_rec_transfer_thms = if forall is_none absT_info_opts
      then
        let
          val pre_rels =
            @{map 2} (fn Ds => mk_rel_of_mrbnf Ds (As @ co_rec_Xs) (Bs @ co_rec_Ys) Bounds Frees) Dss pre_mrbnfs;
          val rels = @{map 3} (fn T => fn T' => Thm.prop_of #> HOLogic.dest_Trueprop
              #> fst o dest_comb #> fst o dest_comb #> funpow n (snd o dest_comb)
              #> case_fp fp (fst o dest_comb #> snd o dest_comb) (snd o dest_comb) #> head_of
              #> force_typ names_lthy (ABphiTs ---> mk_pred2T T T'))
            Ts Us xtor_un_fold_transfers;

          fun tac {context = ctxt, prems = _} = mk_xtor_co_rec_transfer_tac ctxt fp n m co_rec_defs
            xtor_un_fold_transfers map_transfers xtor_rels;

          val mk_rel_co_product = case_fp fp mk_rel_prod mk_rel_sum;
          val rec_phis =
            map2 (fn rel => mk_rel_co_product (Term.list_comb (rel, ABphis))) rels XYphis;
        in
          mk_xtor_co_iter_transfer_thms fp pre_rels rec_phis XYphis rels ABphis
            co_recs (map (subst_atomic_types (ABs @ XYs)) co_recs) tac lthy
        end
      else
        replicate n TrueI (* FIXME *);

    val notes =
      [(case_fp fp ctor_recN dtor_corecN, xtor_co_rec_thms),
       (case_fp fp ctor_rec_uniqueN dtor_corec_uniqueN, split_conj_thm xtor_co_rec_unique_thm),
       (case_fp fp ctor_rec_o_mapN dtor_corec_o_mapN, xtor_co_rec_o_map_thms),
       (case_fp fp ctor_rec_transferN dtor_corec_transferN, xtor_co_rec_transfer_thms)]
      |> map (apsnd (map single))
      |> maps (fn (thmN, thmss) =>
        map2 (fn b => fn thms =>
          ((Binding.qualify true (Binding.name_of b) (Binding.name thmN), []), [(thms, [])]))
        bs thmss);

     val lthy = lthy |> Config.get lthy mrbnf_internals ? snd o Local_Theory.notes notes;
  in
    ((co_recs,
     (xtor_co_rec_thms, xtor_co_rec_unique_thm, xtor_co_rec_o_map_thms, xtor_co_rec_transfer_thms)),
      lthy)
  end;

fun fixpoint_mrbnf force_out_of_line extra_qualify construct_fp bs resBs Ds0 Xs rhsXs var_typess comp_cache0
    lthy =
  let
    val time = time lthy;
    val timer = time (Timer.startRealTimer ());

    fun flatten_tyargs Ass =
      subtract (op =) Xs (filter (fn T => exists (fn Ts => member (op =) Ts T) Ass) resBs) @ Xs;

    val ((mrbnfs, (deadss, livess)), (comp_cache_unfold_set, lthy')) =
      apfst (apsnd split_list o split_list)
        (@{fold_map 3}
          (fn b => mrbnf_of_typ true Smart_Inline (raw_qualify extra_qualify b) flatten_tyargs Xs Ds0)
          bs var_typess rhsXs ((comp_cache0, empty_unfolds), lthy));

    fun norm_qualify i =
      Binding.qualify true (Binding.name_of (nth bs (Int.max (0, i - 1))))
      #> extra_qualify #> Binding.concealed;

    val Ass = map (map dest_TFree) livess;
    val Ds' = fold (fold Term.add_tfreesT) deadss [];
    val Ds = union (op =) Ds' Ds0;
    val missing = resBs |> fold (subtract (op =)) (Ds' :: Ass);
    val (dead_phantoms, live_phantoms) = List.partition (member (op =) Ds0) missing;
    val resBs' = resBs |> fold (subtract (op =)) [dead_phantoms, Ds];

    val timer = time (timer "Construction of MRBNFs");

    val ((kill_posss, _), _, (mrbnfs', ((comp_cache', unfold_set'), lthy''))) =
      normalize_mrbnfs norm_qualify [] Ass Ds (K (resBs' @ Xs)) NONE mrbnfs (comp_cache_unfold_set, lthy');

    val Dss = @{map 3} (fn lives => fn kill_posss => fn deads => deads @ map (nth lives) kill_posss)
      livess kill_posss deadss;
    val all_Dss = Dss |> force_out_of_line ? map (fn Ds' => union (op =) Ds' (map TFree Ds0));

    fun pre_qualify b =
      Binding.qualify false (Binding.name_of b)
      #> extra_qualify
      #> not (Config.get lthy'' mrbnf_internals) ? Binding.concealed;

    val ((pre_mrbnfs, (deadss, absT_infos)), lthy''') = lthy''
      |> @{fold_map 5} (fn b => seal_mrbnf (pre_qualify b) unfold_set' (Binding.prefix_name preN b))
        bs (replicate (length rhsXs) (force_out_of_line orelse not (null live_phantoms))) Dss
        all_Dss mrbnfs'
      |>> split_list
      |>> apsnd split_list;

    val timer = time (timer "Normalization & sealing of MRBNFs");

    val res = construct_fp bs resBs (map TFree dead_phantoms, deadss) pre_mrbnfs absT_infos lthy''';

    val timer = time (timer "FP construction in total");
  in
    (((pre_mrbnfs, absT_infos), comp_cache'), res)
  end;

end;