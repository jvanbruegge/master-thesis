signature MRBNF_FP_DEF_SUGAR =
sig
  type fp_sugar =
    {T: typ,
     BT: typ,
     X: typ,
     fp: MRBNF_Util.fp_kind,
     fp_res_index: int,
     fp_res: MRBNF_FP_Util.fp_result,
     pre_mrbnf: MRBNF_Def.mrbnf,
     fp_mrbnf: MRBNF_Def.mrbnf,
     absT_info: MRBNF_Comp.absT_info,
     fp_nesting_mrbnfs: MRBNF_Def.mrbnf list,
     live_nesting_mrbnfs: MRBNF_Def.mrbnf list,
     fp_ctr_sugar: BNF_FP_Def_Sugar.fp_ctr_sugar,
     fp_bnf_sugar: BNF_FP_Def_Sugar.fp_bnf_sugar,
     fp_co_induct_sugar: BNF_FP_Def_Sugar.fp_co_induct_sugar option}

  val morph_fp_sugar: morphism -> fp_sugar -> fp_sugar

  val co_datatypes: BNF_Util.fp_kind -> (mixfix list -> binding list -> binding list ->
      binding list -> binding list list -> binding list -> (string * sort) list ->
      typ list * typ list list -> MRBNF_Def.mrbnf list -> MRBNF_Comp.absT_info list -> local_theory ->
      MRBNF_FP_Util.fp_result * local_theory) ->
    Ctr_Sugar.ctr_options
    * ((((((binding option * (typ * sort)) list * binding) * mixfix)
         * ((binding, binding * typ) Ctr_Sugar.ctr_spec * mixfix) list) *
         (binding * binding * binding))
       * term list) list ->
    local_theory -> local_theory

  val derive_map_set_rel_pred_thms: (string -> bool) -> MRBNF_Util.fp_kind -> int -> int -> int -> typ list ->
    typ list -> typ -> typ -> thm list -> thm list -> thm list -> thm list -> thm list ->
    thm list -> thm list -> thm list -> thm list -> string -> MRBNF_Def.mrbnf -> MRBNF_Def.mrbnf list ->
    typ -> term -> thm -> thm -> thm -> thm list -> thm -> thm -> thm list -> thm -> thm list ->
    thm list -> thm list -> typ list list -> Ctr_Sugar.ctr_sugar -> local_theory ->
    (thm list * thm list * thm list list * thm list * thm list * thm list * thm list * thm list
     * thm list * thm list * thm list list list list * thm list list list list * thm list
     * thm list * thm list * thm list * thm list) * local_theory

  val derive_induct_recs_thms_for_types: (string -> bool) -> MRBNF_Def.mrbnf list ->
     ('a * typ list list list list * term list list * 'b) option -> thm -> thm list ->
     MRBNF_Def.mrbnf list -> MRBNF_Def.mrbnf list -> typ list -> typ list -> typ list ->
     typ list list list -> thm list -> thm list -> thm list -> term list list -> thm list list ->
     term list -> thm list -> Proof.context -> BNF_FP_Def_Sugar.lfp_sugar_thms

  val nesting_mrbnfs: Proof.context -> typ list list list -> typ list -> MRBNF_Def.mrbnf list
end;

structure MRBNF_FP_Def_Sugar : MRBNF_FP_DEF_SUGAR =
struct

open BNF_Util
open BNF_FP_Def_Sugar
open BNF_FP_Def_Sugar_Tactics
open BNF_FP_Util
open Ctr_Sugar
open MRBNF_Def
open MRBNF_Comp
(*open Ctr_Sugar
open BNF_FP_Rec_Sugar_Util
open BNF_Comp
open BNF_Def
open BNF_FP_Util
open BNF_FP_Def_Sugar_Tactics*)

type fp_sugar =
  {T: typ,
   BT: typ,
   X: typ,
   fp: MRBNF_Util.fp_kind,
   fp_res_index: int,
   fp_res: MRBNF_FP_Util.fp_result,
   pre_mrbnf: MRBNF_Def.mrbnf,
   fp_mrbnf: MRBNF_Def.mrbnf,
   absT_info: MRBNF_Comp.absT_info,
   fp_nesting_mrbnfs: MRBNF_Def.mrbnf list,
   live_nesting_mrbnfs: MRBNF_Def.mrbnf list,
   fp_ctr_sugar: BNF_FP_Def_Sugar.fp_ctr_sugar,
   fp_bnf_sugar: BNF_FP_Def_Sugar.fp_bnf_sugar,
   fp_co_induct_sugar: BNF_FP_Def_Sugar.fp_co_induct_sugar option}

fun morph_fp_sugar phi ({T, BT, X, fp, fp_res, fp_res_index, pre_mrbnf, fp_mrbnf, absT_info,
    fp_nesting_mrbnfs, live_nesting_mrbnfs, fp_ctr_sugar, fp_bnf_sugar,
    fp_co_induct_sugar} : fp_sugar) =
  {T = Morphism.typ phi T,
   BT = Morphism.typ phi BT,
   X = Morphism.typ phi X,
   fp = fp,
   fp_res = MRBNF_FP_Util.morph_fp_result phi fp_res,
   fp_res_index = fp_res_index,
   pre_mrbnf = morph_mrbnf phi pre_mrbnf,
   fp_mrbnf = morph_mrbnf phi fp_mrbnf,
   absT_info = morph_absT_info phi absT_info,
   fp_nesting_mrbnfs = map (morph_mrbnf phi) fp_nesting_mrbnfs,
   live_nesting_mrbnfs = map (morph_mrbnf phi) live_nesting_mrbnfs,
   fp_ctr_sugar = morph_fp_ctr_sugar phi fp_ctr_sugar,
   fp_bnf_sugar = morph_fp_bnf_sugar phi fp_bnf_sugar,
   fp_co_induct_sugar = Option.map (morph_fp_co_induct_sugar phi) fp_co_induct_sugar};

fun liveness_of_fp_mrbnf n mrbnf =
  (case T_of_mrbnf mrbnf of
    Type (_, Ts) => map (not o member (op =) (deads_of_mrbnf mrbnf)) Ts
  | _ => replicate n false);

fun add_nesting_mrbnf_names Us =
  let
    fun add (Type (s, Ts)) ss =
        let val (needs, ss') = fold_map add Ts ss in
          if exists I needs then (true, insert (op =) s ss') else (false, ss')
        end
      | add T ss = (member (op =) Us T, ss);
  in snd oo add end;

val case_transferN = "case_transfer";
val set0N = "set0";
val case_transferN = "case_transfer";
val ctr_transferN = "ctr_transfer";
val disc_transferN = "disc_transfer";
val sel_transferN = "sel_transfer";
val map_disc_iffN = "map_disc_iff";
val map_selN = "map_sel";
val pred_injectN = "pred_inject";
val set_casesN = "set_cases";
val set_introsN = "set_intros";
val set_selN = "set_sel";
val rec_o_mapN = "rec_o_map";
val rec_transferN = "rec_transfer";
val set_inductN = "set_induct";
val corec_codeN = "corec_code";
val corec_transferN = "corec_transfer";
val map_o_corecN = "map_o_corec";

fun nesting_mrbnfs ctxt ctr_Tsss Us =
  map_filter (mrbnf_of ctxt) (fold (fold (fold (add_nesting_mrbnf_names Us))) ctr_Tsss []);

fun choose_binary_fun fs AB =
  find_first (fastype_of #> binder_types #> (fn [A, B] => AB = (A, B))) fs;
fun build_binary_fun_app fs t u =
  Option.map (rapp u o rapp t) (choose_binary_fun fs (fastype_of t, fastype_of u));

fun build_the_rel ctxt Rs Ts A B =
  build_rel [] ctxt Ts [] (the o choose_binary_fun Rs) (A, B);
fun build_rel_app ctxt Rs Ts t u =
  build_the_rel ctxt Rs Ts (fastype_of t) (fastype_of u) $ t $ u;

fun build_set_app ctxt A t = Term.betapply (build_set ctxt A (fastype_of t), t);

fun mk_flip (x, Type (_, [T1, Type (_, [T2, T3])])) =
  Abs ("x", T1, Abs ("y", T2, Var (x, T2 --> T1 --> T3) $ Bound 0 $ Bound 1));

fun flip_rels ctxt n thm =
  let
    val Rs = Term.add_vars (Thm.prop_of thm) [];
    val Rs' = rev (drop (length Rs - n) Rs);
  in
    infer_instantiate ctxt (map (fn f => (fst f, Thm.cterm_of ctxt (mk_flip f))) Rs') thm
  end;

fun uncurry_thm 0 thm = thm
  | uncurry_thm 1 thm = thm
  | uncurry_thm n thm = rotate_prems ~1 (uncurry_thm (n - 1) (rotate_prems 1 (conjI RS thm)));

fun zipper_map f =
  let
    fun zed _ [] = []
      | zed xs (y :: ys) = f (xs, y, ys) :: zed (xs @ [y]) ys;
  in zed [] end;

val name_of_set = name_of_const "set function" domain_type;

val nitpicksimp_attrs = @{attributes [nitpick_simp]};
val simp_attrs = @{attributes [simp]};

structure Data = Generic_Data
(
  type T = fp_sugar Symtab.table;
  val empty = Symtab.empty;
  fun merge data : T = Symtab.merge (K true) data;
);

structure FP_Sugar_Plugin = Plugin(type T = fp_sugar list);

val register_fp_sugars_raw =
  fold (fn fp_sugar as {T = Type (s, _), ...} =>
    Local_Theory.declaration {syntax = false, pervasive = true}
      (fn phi => Data.map (Symtab.update (s, morph_fp_sugar phi fp_sugar))));

val interpret_fp_sugars = FP_Sugar_Plugin.data;

fun interpret_mrbnfs_register_fp_sugars plugins Ts BTs Xs fp pre_mrbnfs absT_infos fp_nesting_mrbnfs
    live_nesting_mrbnfs fp_res ctrXs_Tsss ctor_iff_dtors ctr_defss ctr_sugars co_recs co_rec_defs
    map_thmss common_co_inducts co_inductss co_rec_thmss co_rec_discss co_rec_selsss rel_injectss
    rel_distinctss map_disc_iffss map_selsss rel_selss rel_intross rel_casess pred_injectss
    set_thmss set_selsssss set_introsssss set_casess ctr_transferss case_transferss disc_transferss
    sel_transferss co_rec_disc_iffss co_rec_codess co_rec_transferss common_rel_co_inducts
    rel_co_inductss common_set_inducts set_inductss co_rec_o_mapss noted =
  let
    val fp_sugars =
      map_index (fn (kk, T) =>
        {T = T, BT = nth BTs kk, X = nth Xs kk, fp = fp, fp_res = fp_res, fp_res_index = kk,
         pre_mrbnf = nth pre_mrbnfs kk, absT_info = nth absT_infos kk,
         fp_mrbnf = nth (#mrbnfs fp_res) kk,
         fp_nesting_mrbnfs = fp_nesting_mrbnfs, live_nesting_mrbnfs = live_nesting_mrbnfs,
         fp_ctr_sugar =
           {ctrXs_Tss = nth ctrXs_Tsss kk,
            ctor_iff_dtor = nth ctor_iff_dtors kk,
            ctr_defs = nth ctr_defss kk,
            ctr_sugar = nth ctr_sugars kk,
            ctr_transfers = nth ctr_transferss kk,
            case_transfers = nth case_transferss kk,
            disc_transfers = nth disc_transferss kk,
            sel_transfers = nth sel_transferss kk},
         fp_bnf_sugar =
           {map_thms = nth map_thmss kk,
            map_disc_iffs = nth map_disc_iffss kk,
            map_selss = nth map_selsss kk,
            rel_injects = nth rel_injectss kk,
            rel_distincts = nth rel_distinctss kk,
            rel_sels = nth rel_selss kk,
            rel_intros = nth rel_intross kk,
            rel_cases = nth rel_casess kk,
            pred_injects = nth pred_injectss kk,
            set_thms = nth set_thmss kk,
            set_selssss = nth set_selsssss kk,
            set_introssss = nth set_introsssss kk,
            set_cases = nth set_casess kk},
         fp_co_induct_sugar = SOME
           {co_rec = nth co_recs kk,
            common_co_inducts = common_co_inducts,
            co_inducts = nth co_inductss kk,
            co_rec_def = nth co_rec_defs kk,
            co_rec_thms = nth co_rec_thmss kk,
            co_rec_discs = nth co_rec_discss kk,
            co_rec_disc_iffs = nth co_rec_disc_iffss kk,
            co_rec_selss = nth co_rec_selsss kk,
            co_rec_codes = nth co_rec_codess kk,
            co_rec_transfers = nth co_rec_transferss kk,
            co_rec_o_maps = nth co_rec_o_mapss kk,
            common_rel_co_inducts = common_rel_co_inducts,
            rel_co_inducts = nth rel_co_inductss kk,
            common_set_inducts = common_set_inducts,
            set_inducts = nth set_inductss kk}}
        |> morph_fp_sugar (substitute_noted_thm noted)) Ts;
  in
    register_fp_sugars_raw fp_sugars
    #> fold (interpret_mrbnf plugins) (#mrbnfs fp_res)
    #> interpret_fp_sugars plugins fp_sugars
  end;

fun quasi_unambiguous_case_names names =
  let
    val ps = map (`Long_Name.base_name) names;
    val dups = Library.duplicates (op =) (map fst ps);
    fun underscore s =
      let val ss = Long_Name.explode s
      in space_implode "_" (drop (length ss - 2) ss) end;
  in
    map (fn (base, full) => if member (op =) dups base then underscore full else base) ps
    |> Name.variant_list []
  end;

fun interlace [] _ _ _ = []
  | interlace (Live_Var::var_types) (l::lives) bounds frees = l::interlace var_types lives bounds frees
  | interlace (Bound_Var::var_types) lives (b::bounds) frees = b::interlace var_types lives bounds frees
  | interlace (Free_Var::var_types) lives bounds (f::frees) = f::interlace var_types lives bounds frees

fun mk_mrbnf_sets mrbnf =
  let
    val Type (T_name, Us) = T_of_mrbnf mrbnf;
    val lives = lives_of_mrbnf mrbnf;
    val bounds = bounds_of_mrbnf mrbnf;
    val frees = frees_of_mrbnf mrbnf
    val sets = sets_of_mrbnf mrbnf;
    val vars = interlace (var_types_of_mrbnf mrbnf) lives bounds frees;
    fun mk_set U =
      (case find_index (curry (op =) U) vars of
        ~1 => Term.dummy
      | i => nth sets i);
  in
    (T_name, map mk_set Us)
  end;

val lists_bmoc = fold (fn xs => fn t => Term.list_comb (t, xs));

fun indexify proj xs f p = f (find_index (curry (op =) (proj p)) xs) p;

fun derive_map_set_rel_pred_thms plugins fp live bound free As Bs C E abs_inverses ctr_defs fp_nesting_set_maps
    fp_nesting_rel_eq_onps live_nesting_map_id0s live_nesting_set_maps live_nesting_rel_eqs
    live_nesting_rel_eq_onps fp_nested_rel_eq_onps fp_b_name fp_mrbnf fp_mrbnfs fpT ctor ctor_dtor
    dtor_ctor pre_map_def pre_set_defs pre_rel_def fp_map_thm fp_set_thms fp_rel_thm
    extra_unfolds_map extra_unfolds_set extra_unfolds_rel ctr_Tss
    ({casex, case_thms, discs, selss, sel_defs, ctrs, exhaust, exhaust_discs, disc_thmss, sel_thmss,
      injects, distincts, distinct_discsss, ...} : ctr_sugar)
    lthy =
  let
    val n = length ctr_Tss;
    val ms = map length ctr_Tss;

    val B_ify_T = Term.typ_subst_atomic (As ~~ Bs);

    val fpBT = B_ify_T fpT;
    val live_AsBs = filter (op <>) (As ~~ Bs);
    val live_As = map fst live_AsBs;
    val fTs = map (op -->) live_AsBs;

    val ((((((((xss, yss), fs), Ps), Rs), ta), tb), thesis), names_lthy) = lthy
      |> fold (fold Variable.declare_typ) [As, Bs]
      |> mk_Freess "x" ctr_Tss
      ||>> mk_Freess "y" (map (map B_ify_T) ctr_Tss)
      ||>> mk_Frees "f" fTs
      ||>> mk_Frees "P" (map mk_pred1T live_As)
      ||>> mk_Frees "R" (map (uncurry mk_pred2T) live_AsBs)
      ||>> yield_singleton (mk_Frees "a") fpT
      ||>> yield_singleton (mk_Frees "b") fpBT
      ||>> apfst HOLogic.mk_Trueprop o yield_singleton (mk_Frees "thesis") HOLogic.boolT;

    val ctrAs = map (mk_ctr As) ctrs;
    val ctrBs = map (mk_ctr Bs) ctrs;

    val ctr_defs' =
      map2 (fn m => fn def => mk_unabs_def m (HOLogic.mk_obj_eq def)) ms ctr_defs;

    val ABfs = live_AsBs ~~ fs;

    fun derive_rel_case relAsBs rel_inject_thms rel_distinct_thms =
      let
        val rel_Rs_a_b = list_comb (relAsBs, Rs) $ ta $ tb;

        fun mk_assms ctrA ctrB ctxt =
          let
            val argA_Ts = binder_types (fastype_of ctrA);
            val argB_Ts = binder_types (fastype_of ctrB);
            val ((argAs, argBs), names_ctxt) = ctxt
              |> mk_Frees "x" argA_Ts
              ||>> mk_Frees "y" argB_Ts;
            val ctrA_args = list_comb (ctrA, argAs);
            val ctrB_args = list_comb (ctrB, argBs);
          in
            (fold_rev Logic.all (argAs @ argBs) (Logic.list_implies
               (mk_Trueprop_eq (ta, ctrA_args) :: mk_Trueprop_eq (tb, ctrB_args) ::
                  map2 (HOLogic.mk_Trueprop oo build_rel_app lthy Rs []) argAs argBs,
                thesis)),
             names_ctxt)
          end;

        val (assms, names_lthy) = @{fold_map 2} mk_assms ctrAs ctrBs names_lthy;
        val goal = Logic.list_implies (HOLogic.mk_Trueprop rel_Rs_a_b :: assms, thesis);
      in
        Goal.prove_sorry lthy [] [] goal (fn {context = ctxt, prems = _} =>
          mk_rel_case_tac ctxt (Thm.cterm_of ctxt ta) (Thm.cterm_of ctxt tb) exhaust injects
            rel_inject_thms distincts rel_distinct_thms live_nesting_rel_eqs)
        |> singleton (Proof_Context.export names_lthy lthy)
        |> Thm.close_derivation \<^here>
      end;

    fun derive_case_transfer rel_case_thm =
      let
        val (S, names_lthy) = yield_singleton (mk_Frees "S") (mk_pred2T C E) names_lthy;
        val caseA = mk_case As C casex;
        val caseB = mk_case Bs E casex;
        val goal = mk_parametricity_goal names_lthy (S :: Rs) caseA caseB;
      in
        Goal.prove_sorry lthy [] [] goal (fn {context = ctxt, prems = _} =>
          mk_case_transfer_tac ctxt rel_case_thm case_thms)
        |> singleton (Proof_Context.export names_lthy lthy)
        |> Thm.close_derivation \<^here>
      end;
  in
    if live = 0 then
      if plugins transfer_plugin then
        let
          val relAsBs = HOLogic.eq_const fpT;
          val rel_case_thm = derive_rel_case relAsBs [] [];

          val case_transfer_thm = derive_case_transfer rel_case_thm;

          val notes =
            [(case_transferN, [case_transfer_thm], K [])]
            |> massage_simple_notes fp_b_name;

          val (noted, lthy') = lthy
            |> Local_Theory.notes notes;

          val subst = Morphism.thm (substitute_noted_thm noted);
        in
          (([], [], [], [], [], [], [], [], [], [], [], [], [], [], [subst case_transfer_thm], [],
            []), lthy')
        end
      else
        (([], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []), lthy)
    else
      let
        val mapx = mk_map live bound free As Bs (map_of_mrbnf fp_mrbnf);
        val relAsBs = mk_rel live bound free As Bs (rel_of_mrbnf fp_mrbnf);
        val setAs = map (mk_set As) (sets_of_mrbnf fp_mrbnf);
        val discAs = map (mk_disc_or_sel As) discs;
        val discBs = map (mk_disc_or_sel Bs) discs;
        val selAss = map (map (mk_disc_or_sel As)) selss;
        val selBss = map (map (mk_disc_or_sel Bs)) selss;

        val map_ctor_thm =
          if fp = Least_FP then
            fp_map_thm
          else
            let
              val ctorA = mk_ctor As ctor;
              val ctorB = mk_ctor Bs ctor;

              val y_T = domain_type (fastype_of ctorA);
              val (y as Free (y_s, _), _) = lthy
                |> yield_singleton (mk_Frees "y") y_T;

              val ctor_cong =
                infer_instantiate' lthy [NONE, NONE, SOME (Thm.cterm_of lthy ctorB)] arg_cong;
              val fp_map_thm' = fp_map_thm
                |> infer_instantiate' lthy (replicate live NONE @
                  [SOME (Thm.cterm_of lthy (ctorA $ y))])
                |> unfold_thms lthy [dtor_ctor];
            in
              (fp_map_thm' RS ctor_cong RS (ctor_dtor RS sym RS trans))
              |> Drule.generalize (Names.empty, Names.make_set [y_s])
            end;

        val map_thms =
          let
            fun mk_goal ctrA ctrB xs ys =
              let
                val fmap = list_comb (mapx, fs);

                fun mk_arg (x as Free (_, T)) (Free (_, U)) =
                  if T = U then x
                  else build_map lthy [] [] (the o AList.lookup (op =) ABfs) (T, U) $ x;

                val xs' = map2 mk_arg xs ys;
              in
                mk_Trueprop_eq (fmap $ list_comb (ctrA, xs), list_comb (ctrB, xs'))
              end;

            val goals = @{map 4} mk_goal ctrAs ctrBs xss yss;
            val goal = Logic.mk_conjunction_balanced goals;
            val vars = Variable.add_free_names lthy goal [];
          in
            Goal.prove_sorry lthy vars [] goal (fn {context = ctxt, prems = _} =>
              mk_map_tac ctxt abs_inverses pre_map_def map_ctor_thm live_nesting_map_id0s ctr_defs'
                extra_unfolds_map)
            |> Thm.close_derivation \<^here>
            |> Conjunction.elim_balanced (length goals)
          end;

        val set0_thms =
          let
            fun mk_goal A setA ctrA xs =
              let
                val sets = map (build_set_app lthy A)
                  (filter (exists_subtype_in [A] o fastype_of) xs);
              in
                mk_Trueprop_eq (setA $ list_comb (ctrA, xs),
                  (if null sets then HOLogic.mk_set A [] else Library.foldl1 mk_union sets))
              end;

            val goals =
              @{map 2} (fn live_A => fn setA => map2 (mk_goal live_A setA) ctrAs xss) live_As setAs
              |> flat;
          in
            if null goals then
              []
            else
              let
                val goal = Logic.mk_conjunction_balanced goals;
                val vars = Variable.add_free_names lthy goal [];
              in
                Goal.prove_sorry lthy vars [] goal (fn {context = ctxt, prems = _} =>
                  mk_set0_tac ctxt abs_inverses pre_set_defs dtor_ctor fp_set_thms
                    fp_nesting_set_maps live_nesting_set_maps ctr_defs' extra_unfolds_set)
                |> Thm.close_derivation \<^here>
                |> Conjunction.elim_balanced (length goals)
              end
          end;
        val set_thms = set0_thms
          |> map (unfold_thms lthy @{thms insert_is_Un[THEN sym] Un_empty_left Un_insert_left});

        val rel_ctor_thm =
          if fp = Least_FP then
            fp_rel_thm
          else
            let
              val ctorA = mk_ctor As ctor;
              val ctorB = mk_ctor Bs ctor;

              val y_T = domain_type (fastype_of ctorA);
              val z_T = domain_type (fastype_of ctorB);
              val ((y as Free (y_s, _), z as Free (z_s, _)), _) = lthy
                |> yield_singleton (mk_Frees "y") y_T
                ||>> yield_singleton (mk_Frees "z") z_T;
            in
              fp_rel_thm
              |> infer_instantiate' lthy (replicate live NONE @
                [SOME (Thm.cterm_of lthy (ctorA $ y)), SOME (Thm.cterm_of lthy (ctorB $ z))])
              |> unfold_thms lthy [dtor_ctor]
              |> Drule.generalize (Names.empty, Names.make_set [y_s, z_s])
            end;

        val rel_inject_thms =
          let
            fun mk_goal ctrA ctrB xs ys =
              let
                val lhs = list_comb (relAsBs, Rs) $ list_comb (ctrA, xs) $ list_comb (ctrB, ys);
                val conjuncts = map2 (build_rel_app lthy Rs []) xs ys;
              in
                HOLogic.mk_Trueprop
                  (if null conjuncts then lhs
                   else HOLogic.mk_eq (lhs, Library.foldr1 HOLogic.mk_conj conjuncts))
              end;

            val goals = @{map 4} mk_goal ctrAs ctrBs xss yss;
            val goal = Logic.mk_conjunction_balanced goals;
            val vars = Variable.add_free_names lthy goal [];
          in
            Goal.prove_sorry lthy vars [] goal (fn {context = ctxt, prems = _} =>
              mk_rel_tac ctxt abs_inverses pre_rel_def rel_ctor_thm live_nesting_rel_eqs ctr_defs'
                extra_unfolds_rel)
            |> Thm.close_derivation \<^here>
            |> Conjunction.elim_balanced (length goals)
          end;

        val half_rel_distinct_thmss =
          let
            fun mk_goal ((ctrA, xs), (ctrB, ys)) =
              HOLogic.mk_Trueprop (HOLogic.mk_not
                (list_comb (relAsBs, Rs) $ list_comb (ctrA, xs) $ list_comb (ctrB, ys)));

            val rel_infos = (ctrAs ~~ xss, ctrBs ~~ yss);

            val goalss = map (map mk_goal) (mk_half_pairss rel_infos);
            val goals = flat goalss;
          in
            unflat goalss
              (if null goals then
                 []
               else
                 let
                   val goal = Logic.mk_conjunction_balanced goals;
                   val vars = Variable.add_free_names lthy goal [];
                 in
                   Goal.prove_sorry lthy vars [] goal (fn {context = ctxt, prems = _} =>
                     mk_rel_tac ctxt abs_inverses pre_rel_def rel_ctor_thm live_nesting_rel_eqs
                       ctr_defs' extra_unfolds_rel)
                   |> Thm.close_derivation \<^here>
                   |> Conjunction.elim_balanced (length goals)
                 end)
          end;

        val rel_flip = rel_flip_of_mrbnf fp_mrbnf;

        fun mk_other_half_rel_distinct_thm thm =
          flip_rels lthy live thm RS (rel_flip RS sym RS @{thm arg_cong[of _ _ Not]} RS iffD2);

        val other_half_rel_distinct_thmss =
          map (map mk_other_half_rel_distinct_thm) half_rel_distinct_thmss;
        val (rel_distinct_thms, _) =
          join_halves n half_rel_distinct_thmss other_half_rel_distinct_thmss;

        fun mk_rel_intro_thm m thm =
          uncurry_thm m (thm RS iffD2) handle THM _ => thm;

        val rel_intro_thms = map2 mk_rel_intro_thm ms rel_inject_thms;

        val rel_code_thms =
          map (fn thm => thm RS @{thm eq_False[THEN iffD2]}) rel_distinct_thms @
          map2 (fn thm => fn 0 => thm RS @{thm eq_True[THEN iffD2]} | _ => thm) rel_inject_thms ms;

        val ctr_transfer_thms =
          let
            val goals = map2 (mk_parametricity_goal names_lthy Rs) ctrAs ctrBs;
            val goal = Logic.mk_conjunction_balanced goals;
            val vars = Variable.add_free_names lthy goal [];
          in
            Goal.prove_sorry lthy vars [] goal
              (fn {context = ctxt, prems = _} =>
                 mk_ctr_transfer_tac ctxt rel_intro_thms live_nesting_rel_eqs)
            |> Thm.close_derivation \<^here>
            |> Conjunction.elim_balanced (length goals)
          end;

        val (set_cases_thms, set_cases_attrss) =
          let
            fun mk_prems assms elem t ctxt =
              (case fastype_of t of
                Type (type_name, xs) =>
                (case mrbnf_of ctxt type_name of
                  NONE => ([], ctxt)
                | SOME mrbnf =>
                  apfst flat (fold_map (fn set => fn ctxt =>
                    let
                      val T = HOLogic.dest_setT (range_type (fastype_of set));
                      val new_var = not (T = fastype_of elem);
                      val (x, ctxt') =
                        if new_var then yield_singleton (mk_Frees "x") T ctxt else (elem, ctxt);
                    in
                      mk_prems (mk_Trueprop_mem (x, set $ t) :: assms) elem x ctxt'
                      |>> map (new_var ? Logic.all x)
                    end) (map (mk_set xs) (sets_of_mrbnf mrbnf)) ctxt))
              | T => rpair ctxt
                (if T = fastype_of elem then [fold (curry Logic.mk_implies) assms thesis] else []));
          in
            split_list (map (fn set =>
              let
                val A = HOLogic.dest_setT (range_type (fastype_of set));
                val (elem, names_lthy) = yield_singleton (mk_Frees "e") A names_lthy;
                val premss =
                  map (fn ctr =>
                    let
                      val (args, names_lthy) =
                        mk_Frees "z" (binder_types (fastype_of ctr)) names_lthy;
                    in
                      flat (zipper_map (fn (prev_args, arg, next_args) =>
                        let
                          val (args_with_elem, args_without_elem) =
                            if fastype_of arg = A then
                              (prev_args @ [elem] @ next_args, prev_args @ next_args)
                            else
                              `I (prev_args @ [arg] @ next_args);
                        in
                          mk_prems [mk_Trueprop_eq (ta, Term.list_comb (ctr, args_with_elem))]
                            elem arg names_lthy
                          |> fst
                          |> map (fold_rev Logic.all args_without_elem)
                        end) args)
                    end) ctrAs;
                val goal = Logic.mk_implies (mk_Trueprop_mem (elem, set $ ta), thesis);
                val vars = Variable.add_free_names lthy goal [];
                val thm =
                  Goal.prove_sorry lthy vars (flat premss) goal (fn {context = ctxt, prems} =>
                    mk_set_cases_tac ctxt (Thm.cterm_of ctxt ta) prems exhaust set_thms)
                  |> Thm.close_derivation \<^here>
                  |> rotate_prems ~1;

                val cases_set_attr =
                  Attrib.internal (K (Induct.cases_pred (name_of_set set)));

                val ctr_names = quasi_unambiguous_case_names (flat
                  (map (uncurry mk_names o map_prod length name_of_ctr) (premss ~~ ctrAs)));
              in
                (* TODO: @{attributes [elim?]} *)
                (thm, [Attrib.consumes 1, cases_set_attr, Attrib.case_names ctr_names])
              end) setAs)
          end;

        val (set_intros_thmssss, set_intros_thms) =
          let
            fun mk_goals A setA ctr_args t ctxt =
              (case fastype_of t of
                Type (type_name, innerTs) =>
                (case mrbnf_of ctxt type_name of
                  NONE => ([], ctxt)
                | SOME mrbnf =>
                  apfst flat (fold_map (fn set => fn ctxt =>
                    let
                      val T = HOLogic.dest_setT (range_type (fastype_of set));
                      val (y, ctxt') = yield_singleton (mk_Frees "y") T ctxt;
                      val assm = mk_Trueprop_mem (y, set $ t);
                    in
                      apfst (map (Logic.mk_implies o pair assm)) (mk_goals A setA ctr_args y ctxt')
                    end) (map (mk_set innerTs) (sets_of_mrbnf mrbnf)) ctxt))
              | T => (if T = A then [mk_Trueprop_mem (t, setA $ ctr_args)] else [], ctxt));

            val (goalssss, _) =
              fold_map (fn set =>
                let val A = HOLogic.dest_setT (range_type (fastype_of set)) in
                  @{fold_map 2} (fn ctr => fn xs =>
                      fold_map (mk_goals A set (Term.list_comb (ctr, xs))) xs)
                    ctrAs xss
                end) setAs lthy;
            val goals = flat (flat (flat goalssss));
          in
            `(unflattt goalssss)
              (if null goals then
                 []
               else
                 let
                   val goal = Logic.mk_conjunction_balanced goals;
                   val vars = Variable.add_free_names lthy goal [];
                 in
                   Goal.prove_sorry lthy vars [] goal
                     (fn {context = ctxt, prems = _} => mk_set_intros_tac ctxt set0_thms)
                   |> Thm.close_derivation \<^here>
                   |> Conjunction.elim_balanced (length goals)
                 end)
          end;

        val rel_sel_thms =
          let
            val n = length discAs;
            fun mk_conjunct n k discA selAs discB selBs =
              (if k = n then [] else [HOLogic.mk_eq (discA $ ta, discB $ tb)]) @
              (if null selAs then
                 []
               else
                 [Library.foldr HOLogic.mk_imp
                    (if n = 1 then [] else [discA $ ta, discB $ tb],
                     Library.foldr1 HOLogic.mk_conj (map2 (build_rel_app names_lthy Rs [])
                       (map (rapp ta) selAs) (map (rapp tb) selBs)))]);

            val goals =
              if n = 0 then
                []
              else
                [mk_Trueprop_eq (build_rel_app names_lthy Rs [] ta tb,
                   (case flat (@{map 5} (mk_conjunct n) (1 upto n) discAs selAss discBs selBss) of
                     [] => \<^term>\<open>True\<close>
                   | conjuncts => Library.foldr1 HOLogic.mk_conj conjuncts))];

            fun prove goal =
              Variable.add_free_names lthy goal []
              |> (fn vars => Goal.prove_sorry lthy vars [] goal (fn {context = ctxt, prems = _} =>
                mk_rel_sel_tac ctxt (Thm.cterm_of ctxt ta) (Thm.cterm_of ctxt tb) exhaust
                  (flat disc_thmss) (flat sel_thmss) rel_inject_thms distincts rel_distinct_thms
                  live_nesting_rel_eqs))
              |> Thm.close_derivation \<^here>;
          in
            map prove goals
          end;

        val (rel_case_thm, rel_case_attrs) =
          let
            val thm = derive_rel_case relAsBs rel_inject_thms rel_distinct_thms;
            val ctr_names = quasi_unambiguous_case_names (map name_of_ctr ctrAs);
          in
            (thm, [Attrib.case_names ctr_names, Attrib.consumes 1] @ @{attributes [cases pred]})
          end;

        val case_transfer_thm = derive_case_transfer rel_case_thm;

        val sel_transfer_thms =
          if null selAss then
            []
          else
            let
              val shared_sels = foldl1 (uncurry (inter (op =))) (map (op ~~) (selAss ~~ selBss));
              val goals = map (uncurry (mk_parametricity_goal names_lthy Rs)) shared_sels;
            in
              if null goals then
                []
              else
                let
                  val goal = Logic.mk_conjunction_balanced goals;
                  val vars = Variable.add_free_names lthy goal [];
                in
                  Goal.prove_sorry lthy vars [] goal
                    (fn {context = ctxt, prems = _} =>
                       mk_sel_transfer_tac ctxt n sel_defs case_transfer_thm)
                  |> Thm.close_derivation \<^here>
                  |> Conjunction.elim_balanced (length goals)
                end
            end;

        val disc_transfer_thms =
          let val goals = map2 (mk_parametricity_goal names_lthy Rs) discAs discBs in
            if null goals then
              []
            else
              let
                val goal = Logic.mk_conjunction_balanced goals;
                val vars = Variable.add_free_names lthy goal [];
              in
                Goal.prove_sorry lthy vars [] goal
                  (fn {context = ctxt, prems = _} => mk_disc_transfer_tac ctxt
                     (the_single rel_sel_thms) (the_single exhaust_discs)
                     (flat (flat distinct_discsss)))
                |> Thm.close_derivation \<^here>
                |> Conjunction.elim_balanced (length goals)
              end
          end;

        val map_disc_iff_thms =
          let
            val discsB = map (mk_disc_or_sel Bs) discs;
            val discsA_t = map (fn disc1 => Term.betapply (disc1, ta)) discAs;

            fun mk_goal (discA_t, discB) =
              if head_of discA_t aconv HOLogic.Not orelse is_refl_bool discA_t then
                NONE
              else
                SOME (mk_Trueprop_eq (betapply (discB, (Term.list_comb (mapx, fs) $ ta)), discA_t));

            val goals = map_filter mk_goal (discsA_t ~~ discsB);
          in
            if null goals then
              []
            else
              let
                val goal = Logic.mk_conjunction_balanced goals;
                val vars = Variable.add_free_names lthy goal [];
              in
                Goal.prove_sorry lthy vars [] goal
                  (fn {context = ctxt, prems = _} =>
                     mk_map_disc_iff_tac ctxt (Thm.cterm_of ctxt ta) exhaust (flat disc_thmss)
                       map_thms)
                |> Thm.close_derivation \<^here>
                |> Conjunction.elim_balanced (length goals)
              end
          end;

        val (map_sel_thmss, map_sel_thms) =
          let
            fun mk_goal discA selA selB =
              let
                val prem = Term.betapply (discA, ta);
                val lhs = selB $ (Term.list_comb (mapx, fs) $ ta);
                val lhsT = fastype_of lhs;
                val map_rhsT =
                  map_atyps (perhaps (AList.lookup (op =) (map swap live_AsBs))) lhsT;
                val map_rhs = build_map lthy [] []
                  (the o (AList.lookup (op =) (live_AsBs ~~ fs))) (map_rhsT, lhsT);
                val rhs = (case map_rhs of
                    Const (\<^const_name>\<open>id\<close>, _) => selA $ ta
                  | _ => map_rhs $ (selA $ ta));
                val concl = mk_Trueprop_eq (lhs, rhs);
              in
                if is_refl_bool prem then concl
                else Logic.mk_implies (HOLogic.mk_Trueprop prem, concl)
              end;

            val goalss = @{map 3} (map2 o mk_goal) discAs selAss selBss;
            val goals = flat goalss;
          in
            `(unflat goalss)
              (if null goals then
                 []
               else
                 let
                   val goal = Logic.mk_conjunction_balanced goals;
                   val vars = Variable.add_free_names lthy goal [];
                 in
                   Goal.prove_sorry lthy vars [] goal
                     (fn {context = ctxt, prems = _} =>
                        mk_map_sel_tac ctxt (Thm.cterm_of ctxt ta) exhaust (flat disc_thmss)
                          map_thms (flat sel_thmss) live_nesting_map_id0s)
                   |> Thm.close_derivation \<^here>
                   |> Conjunction.elim_balanced (length goals)
                 end)
          end;

        val (set_sel_thmssss, set_sel_thms) =
          let
            fun mk_goal setA discA selA ctxt =
              let
                val prem = Term.betapply (discA, ta);
                val sel_rangeT = range_type (fastype_of selA);
                val A = HOLogic.dest_setT (range_type (fastype_of setA));

                fun travese_nested_types t ctxt =
                  (case fastype_of t of
                    Type (type_name, innerTs) =>
                    (case mrbnf_of ctxt type_name of
                      NONE => ([], ctxt)
                    | SOME mrbnf =>
                      let
                        fun seq_assm a set ctxt =
                          let
                            val T = HOLogic.dest_setT (range_type (fastype_of set));
                            val (x, ctxt') = yield_singleton (mk_Frees "x") T ctxt;
                            val assm = mk_Trueprop_mem (x, set $ a);
                          in
                            travese_nested_types x ctxt'
                            |>> map (Logic.mk_implies o pair assm)
                          end;
                      in
                        fold_map (seq_assm t o mk_set innerTs) (sets_of_mrbnf mrbnf) ctxt
                        |>> flat
                      end)
                  | T =>
                    if T = A then ([mk_Trueprop_mem (t, setA $ ta)], ctxt) else ([], ctxt));

                val (concls, ctxt') =
                  if sel_rangeT = A then ([mk_Trueprop_mem (selA $ ta, setA $ ta)], ctxt)
                  else travese_nested_types (selA $ ta) ctxt;
              in
                if exists_subtype_in [A] sel_rangeT then
                  if is_refl_bool prem then (concls, ctxt')
                  else (map (Logic.mk_implies o pair (HOLogic.mk_Trueprop prem)) concls, ctxt')
                else
                  ([], ctxt)
              end;

            val (goalssss, _) =
              fold_map (fn set => @{fold_map 2} (fold_map o mk_goal set) discAs selAss)
                setAs names_lthy;
            val goals = flat (flat (flat goalssss));
          in
            `(unflattt goalssss)
              (if null goals then
                 []
               else
                 let
                   val goal = Logic.mk_conjunction_balanced goals;
                   val vars = Variable.add_free_names lthy goal [];
                 in
                   Goal.prove_sorry lthy vars [] goal
                     (fn {context = ctxt, prems = _} =>
                        mk_set_sel_tac ctxt (Thm.cterm_of ctxt ta) exhaust (flat disc_thmss)
                          (flat sel_thmss) set0_thms)
                   |> Thm.close_derivation \<^here>
                   |> Conjunction.elim_balanced (length goals)
                 end)
          end;

        val pred_injects =
          let
            val rel_eq_onp_with_tops_of =
              Conv.fconv_rule (HOLogic.Trueprop_conv (Conv.arg1_conv
                (Conv.top_sweep_rewrs_conv @{thms eq_onp_top_eq_eq[symmetric, THEN eq_reflection]} lthy)));

            val eq_onps = map rel_eq_onp_with_tops_of
              (map rel_eq_onp_of_mrbnf fp_mrbnfs @ fp_nesting_rel_eq_onps @ live_nesting_rel_eq_onps @
              fp_nested_rel_eq_onps);
            val cTs = map (SOME o Thm.ctyp_of lthy) (maps (replicate 2) live_As);
            val cts = map (SOME o Thm.cterm_of lthy) (map mk_eq_onp Ps);

            val get_rhs = Thm.concl_of #> HOLogic.dest_Trueprop #> HOLogic.dest_eq #> snd;

            val pred_eq_onp_conj =
              List.foldr (fn (_, thm) => thm RS @{thm eq_onp_live_step}) @{thm refl[of True]};

            fun predify_rel_inject rel_inject =
              let
                val conjuncts = try (get_rhs #> HOLogic.dest_conj) rel_inject |> the_default [];

                fun postproc thm =
                  if null conjuncts then
                    thm RS (@{thm eq_onp_same_args} RS iffD1)
                  else
                    @{thm box_equals} OF [thm, @{thm eq_onp_same_args},
                      pred_eq_onp_conj conjuncts |> unfold_thms lthy @{thms simp_thms(21)}];
              in
                rel_inject
                |> Thm.instantiate' cTs cts
                |> Conv.fconv_rule (HOLogic.Trueprop_conv (Conv.arg_conv
                  (Raw_Simplifier.rewrite lthy false
                     @{thms eq_onp_top_eq_eq[symmetric, THEN eq_reflection]})))
                |> unfold_thms lthy eq_onps
                |> postproc
                |> unfold_thms lthy @{thms top_conj}
              end;
          in
            rel_inject_thms
            |> map (unfold_thms lthy [@{thm conj_assoc}])
            |> map predify_rel_inject
            |> Proof_Context.export names_lthy lthy
          end;

        val anonymous_notes =
          [(rel_code_thms, nitpicksimp_attrs)]
          |> map (fn (thms, attrs) => ((Binding.empty, attrs), [(thms, [])]));

        val notes =
          (if Config.get lthy mrbnf_internals then
             [(set0N, set0_thms, K [])]
           else
             []) @
          [(case_transferN, [case_transfer_thm], K []),
           (ctr_transferN, ctr_transfer_thms, K []),
           (disc_transferN, disc_transfer_thms, K []),
           (sel_transferN, sel_transfer_thms, K []),
           (mapN, map_thms, K (nitpicksimp_attrs @ simp_attrs)),
           (map_disc_iffN, map_disc_iff_thms, K simp_attrs),
           (map_selN, map_sel_thms, K []),
           (pred_injectN, pred_injects, K simp_attrs),
           (rel_casesN, [rel_case_thm], K rel_case_attrs),
           (rel_distinctN, rel_distinct_thms, K simp_attrs),
           (rel_injectN, rel_inject_thms, K simp_attrs),
           (rel_introsN, rel_intro_thms, K []),
           (rel_selN, rel_sel_thms, K []),
           (setN, set_thms, K (case_fp fp nitpicksimp_attrs [] @ simp_attrs)),
           (set_casesN, set_cases_thms, nth set_cases_attrss),
           (set_introsN, set_intros_thms, K []),
           (set_selN, set_sel_thms, K [])]
          |> massage_simple_notes fp_b_name;

        val (noted, lthy') = lthy
          |> uncurry (Spec_Rules.add Binding.empty Spec_Rules.equational)
                (`(single o lhs_head_of o hd) map_thms)
          |> fp = Least_FP ?
              uncurry (Spec_Rules.add Binding.empty Spec_Rules.equational)
                (`(single o lhs_head_of o hd) rel_code_thms)
          |> uncurry (Spec_Rules.add Binding.empty Spec_Rules.equational)
                (`(single o lhs_head_of o hd) set0_thms)
          |> plugins code_plugin ? Code.declare_default_eqns (map (rpair true) (rel_code_thms @ map_thms @ set_thms))
          |> Local_Theory.notes (anonymous_notes @ notes);

        val subst = Morphism.thm (substitute_noted_thm noted);
      in
        ((map subst map_thms,
          map subst map_disc_iff_thms,
          map (map subst) map_sel_thmss,
          map subst rel_inject_thms,
          map subst rel_distinct_thms,
          map subst rel_sel_thms,
          map subst rel_intro_thms,
          [subst rel_case_thm],
          map subst pred_injects,
          map subst set_thms,
          map (map (map (map subst))) set_sel_thmssss,
          map (map (map (map subst))) set_intros_thmssss,
          map subst set_cases_thms,
          map subst ctr_transfer_thms,
          [subst case_transfer_thm],
          map subst disc_transfer_thms,
          map subst sel_transfer_thms), lthy')
      end
  end;

fun derive_induct_recs_thms_for_types plugins pre_mrbnfs rec_args_typess ctor_induct ctor_rec_thms
    live_nesting_mrbnfs fp_nesting_mrbnfs fpTs Cs Xs ctrXs_Tsss pre_abs_inverses pre_type_definitions
    abs_inverses ctrss ctr_defss recs rec_defs ctxt =
  let
    val ctr_Tsss = map (map (binder_types o fastype_of)) ctrss;

    val nn = length pre_mrbnfs;
    val ns = map length ctr_Tsss;
    val mss = map (map length) ctr_Tsss;

    val pre_map_defs = map map_def_of_mrbnf pre_mrbnfs;
    val pre_set_defss = map set_defs_of_mrbnf pre_mrbnfs;
    val live_nesting_map_ident0s = map map_ident0_of_mrbnf live_nesting_mrbnfs;
    val fp_nesting_map_ident0s = map map_ident0_of_mrbnf fp_nesting_mrbnfs;
    val fp_nesting_set_maps = maps set_map_of_mrbnf fp_nesting_mrbnfs;

    val fp_b_names = map base_name_of_typ fpTs;

    val (((ps, xsss), us'), names_ctxt) = ctxt
      |> mk_Frees "P" (map mk_pred1T fpTs)
      ||>> mk_Freesss "x" ctr_Tsss
      ||>> Variable.variant_fixes fp_b_names;

    val us = map2 (curry Free) us' fpTs;

    val setss_fp_nesting = map mk_mrbnf_sets fp_nesting_mrbnfs;

    val (induct_thms, induct_thm) =
      let
        val raw_premss = @{map 4} (@{map 3}
            o mk_induct_raw_prem I names_ctxt (map single Xs) setss_fp_nesting)
          ps ctrss ctr_Tsss ctrXs_Tsss;
        val concl =
          HOLogic.mk_Trueprop (Library.foldr1 HOLogic.mk_conj (map2 (curry (op $)) ps us));
        val goal =
          Library.foldr (Logic.list_implies o apfst (map (finish_induct_prem ctxt nn ps)))
            (raw_premss, concl);
        val vars = Variable.add_free_names ctxt goal [];
        val kksss = map (map (map (fst o snd) o #2)) raw_premss;

        val ctor_induct' = ctor_induct OF (map2 mk_absumprodE pre_type_definitions mss);

        val thm =
          Goal.prove_sorry ctxt vars [] goal (fn {context = ctxt, ...} =>
            mk_induct_tac ctxt nn ns mss kksss (flat ctr_defss) ctor_induct' pre_abs_inverses
              abs_inverses fp_nesting_set_maps pre_set_defss)
          |> Thm.close_derivation \<^here>;
      in
        `(conj_dests nn) thm
      end;

    val xctrss = map2 (map2 (curry Term.list_comb)) ctrss xsss;

    fun mk_rec_thmss (_, x_Tssss, fss, _) recs rec_defs ctor_rec_thms =
      let
        val frecs = map (lists_bmoc fss) recs;

        fun mk_goal frec xctr f xs fxs =
          fold_rev (fold_rev Logic.all) (xs :: fss)
            (mk_Trueprop_eq (frec $ xctr, Term.list_comb (f, fxs)));

        fun maybe_tick (T, U) u f =
          if try (fst o HOLogic.dest_prodT) U = SOME T then
            Term.lambda u (HOLogic.mk_prod (u, f $ u))
          else
            f;

        fun build_rec (x as Free (_, T)) U =
          if T = U then
            x
          else
            let
              val build_simple =
                indexify (perhaps (try (snd o HOLogic.dest_prodT)) o snd) Cs
                  (fn kk => fn TU => maybe_tick TU (nth us kk) (nth frecs kk));
            in
              build_map ctxt [] [] build_simple (T, U) $ x
            end;

        val fxsss = map2 (map2 (flat_rec_arg_args oo map2 (map o build_rec))) xsss x_Tssss;
        val goalss = @{map 5} (@{map 4} o mk_goal) frecs xctrss fss xsss fxsss;

        val tacss = @{map 4} (map ooo
              mk_rec_tac pre_map_defs (fp_nesting_map_ident0s @ live_nesting_map_ident0s) rec_defs)
            ctor_rec_thms pre_abs_inverses abs_inverses ctr_defss;

        fun prove goal tac =
          Goal.prove_sorry ctxt [] [] goal (tac o #context)
          |> Thm.close_derivation \<^here>;
      in
        map2 (map2 prove) goalss tacss
      end;

    val rec_thmss = mk_rec_thmss (the rec_args_typess) recs rec_defs ctor_rec_thms;

  in
    ((induct_thms, induct_thm, mk_induct_attrs ctrss),
     (rec_thmss, nitpicksimp_attrs @ simp_attrs))
  end;

fun mk_induct_attrs ctrss =
  let val induct_cases = quasi_unambiguous_case_names (maps (map name_of_ctr) ctrss);
  in [Attrib.case_names induct_cases] end;

fun postproc_co_induct ctxt nn prop prop_conj =
  Drule.zero_var_indexes
  #> `(conj_dests nn)
  #>> map (fn thm => Thm.permute_prems 0 ~1 (thm RS prop))
  ##> (fn thm => Thm.permute_prems 0 (~ nn)
    (if nn = 1 then thm RS prop
     else funpow nn (fn thm => unfold_thms ctxt @{thms conj_assoc} (thm RS prop_conj)) thm));

fun derive_rel_induct_thms_for_types ctxt nn fpA_Ts As Bs ctrAss ctrAs_Tsss exhausts ctor_rel_induct
    ctor_defss ctor_injects pre_rel_defs abs_inverses live_nesting_rel_eqs =
  let
    val B_ify_T = Term.typ_subst_atomic (As ~~ Bs);
    val B_ify = Term.map_types B_ify_T;

    val fpB_Ts = map B_ify_T fpA_Ts;
    val ctrBs_Tsss = map (map (map B_ify_T)) ctrAs_Tsss;
    val ctrBss = map (map B_ify) ctrAss;

    val ((((Rs, IRs), ctrAsss), ctrBsss), names_ctxt) = ctxt
      |> mk_Frees "R" (map2 mk_pred2T As Bs)
      ||>> mk_Frees "IR" (map2 mk_pred2T fpA_Ts fpB_Ts)
      ||>> mk_Freesss "a" ctrAs_Tsss
      ||>> mk_Freesss "b" ctrBs_Tsss;

    val prems =
      let
        fun mk_prem ctrA ctrB argAs argBs =
          fold_rev Logic.all (argAs @ argBs) (fold_rev (curry Logic.mk_implies)
            (map2 (HOLogic.mk_Trueprop oo build_rel_app names_ctxt (Rs @ IRs) fpA_Ts) argAs argBs)
            (HOLogic.mk_Trueprop (build_rel_app names_ctxt (Rs @ IRs) fpA_Ts
              (Term.list_comb (ctrA, argAs)) (Term.list_comb (ctrB, argBs)))));
      in
        flat (@{map 4} (@{map 4} mk_prem) ctrAss ctrBss ctrAsss ctrBsss)
      end;

    val goal = HOLogic.mk_Trueprop (Library.foldr1 HOLogic.mk_conj (map2 mk_leq
      (map2 (build_the_rel ctxt (Rs @ IRs) []) fpA_Ts fpB_Ts) IRs));
    val vars = Variable.add_free_names ctxt goal [];

    val rel_induct0_thm =
      Goal.prove_sorry ctxt vars prems goal (fn {context = ctxt, prems} =>
        mk_rel_induct0_tac ctxt ctor_rel_induct prems (map (Thm.cterm_of ctxt) IRs) exhausts
          ctor_defss ctor_injects pre_rel_defs abs_inverses live_nesting_rel_eqs)
      |> Thm.close_derivation \<^here>;
  in
    (postproc_co_induct ctxt nn @{thm predicate2D} @{thm predicate2D_conj} rel_induct0_thm,
     mk_induct_attrs ctrAss)
  end;

fun mk_coinduct_strong_thm coind rel_eqs rel_monos mk_vimage2p ctxt =
  let
    val n = Thm.nprems_of coind;
    val m = Thm.nprems_of (hd rel_monos) - n;
    fun mk_inst phi =
      (phi, Thm.cterm_of ctxt (mk_union (Var phi, HOLogic.eq_const (fst (dest_pred2T (#2 phi))))));
    val insts = Term.add_vars (Thm.prop_of coind) [] |> rev |> take n |> map mk_inst;
    fun mk_unfold rel_eq rel_mono =
      let
        val eq = iffD2 OF [rel_eq RS @{thm predicate2_eqD}, refl];
        val mono = rel_mono OF (replicate m @{thm order_refl} @ replicate n @{thm eq_subset});
      in mk_vimage2p (eq RS (mono RS @{thm predicate2D})) RS eqTrueI end;
    val unfolds = map2 mk_unfold rel_eqs rel_monos @ @{thms sup_fun_def sup_bool_def
      imp_disjL all_conj_distrib subst_eq_imp simp_thms(18,21,35)};
  in
    Thm.instantiate (TVars.empty, Vars.make insts) coind
    |> unfold_thms ctxt unfolds
  end;

fun derive_coinduct_thms_for_types ctxt strong alter_r pre_mrbnfs dtor_coinduct dtor_ctors
    live_nesting_mrbnfs fpTs Xs ctrXs_Tsss ns pre_abs_inverses abs_inverses mk_vimage2p ctr_defss
    (ctr_sugars : ctr_sugar list) =
  let
    val nn = length pre_mrbnfs;

    val pre_rel_defs = map rel_def_of_mrbnf pre_mrbnfs;
    val live_nesting_rel_eqs = map rel_eq_of_mrbnf live_nesting_mrbnfs;

    val fp_b_names = map base_name_of_typ fpTs;

    val discss = map #discs ctr_sugars;
    val selsss = map #selss ctr_sugars;
    val exhausts = map #exhaust ctr_sugars;
    val disc_thmsss = map #disc_thmss ctr_sugars;
    val sel_thmsss = map #sel_thmss ctr_sugars;

    val (((rs, us'), vs'), _) = ctxt
      |> mk_Frees "R" (map (fn T => mk_pred2T T T) fpTs)
      ||>> Variable.variant_fixes fp_b_names
      ||>> Variable.variant_fixes (map (suffix "'") fp_b_names);

    val us = map2 (curry Free) us' fpTs;
    val udiscss = map2 (map o rapp) us discss;
    val uselsss = map2 (map o map o rapp) us selsss;

    val vs = map2 (curry Free) vs' fpTs;
    val vdiscss = map2 (map o rapp) vs discss;
    val vselsss = map2 (map o map o rapp) vs selsss;

    val uvrs = @{map 3} (fn r => fn u => fn v => r $ u $ v) rs us vs;
    val uv_eqs = map2 (curry HOLogic.mk_eq) us vs;
    val strong_rs =
      @{map 4} (fn u => fn v => fn uvr => fn uv_eq =>
        fold_rev Term.lambda [u, v] (HOLogic.mk_disj (uvr, uv_eq))) us vs uvrs uv_eqs;

    val concl =
      HOLogic.mk_Trueprop (Library.foldr1 HOLogic.mk_conj
        (@{map 3} (fn uvr => fn u => fn v => HOLogic.mk_imp (uvr, HOLogic.mk_eq (u, v)))
           uvrs us vs))

    fun mk_goal rs0' =
      Logic.list_implies (@{map 9} (mk_coinduct_prem ctxt (map single Xs) (map single fpTs)
            (map alter_r rs0'))
          uvrs us vs ns udiscss uselsss vdiscss vselsss ctrXs_Tsss,
        concl);

    val goals = map mk_goal ([rs] @ (if strong then [strong_rs] else []));

    fun prove dtor_coinduct' goal =
      Variable.add_free_names ctxt goal []
      |> (fn vars => Goal.prove_sorry ctxt vars [] goal (fn {context = ctxt, ...} =>
        mk_coinduct_tac ctxt live_nesting_rel_eqs nn ns dtor_coinduct' pre_rel_defs pre_abs_inverses
          abs_inverses dtor_ctors exhausts ctr_defss disc_thmsss sel_thmsss))
      |> Thm.close_derivation \<^here>;

    val rel_eqs = map rel_eq_of_mrbnf pre_mrbnfs;
    val rel_monos = map rel_mono_of_mrbnf pre_mrbnfs;
    val dtor_coinducts =
      [dtor_coinduct] @
      (if strong then [mk_coinduct_strong_thm dtor_coinduct rel_eqs rel_monos mk_vimage2p ctxt]
       else []);
  in
    map2 (postproc_co_induct ctxt nn mp @{thm conj_commute[THEN iffD1]} oo prove)
      dtor_coinducts goals
  end;

fun derive_coinduct_corecs_thms_for_types ctxt pre_mrbnfs
    (x, cs, cpss, (((pgss, _, _, _), cqgsss), _)) dtor_coinduct dtor_injects dtor_ctors
    dtor_corec_thms live_nesting_mrbnfs fpTs Cs Xs ctrXs_Tsss kss mss ns pre_abs_inverses abs_inverses
    mk_vimage2p ctr_defss (ctr_sugars : ctr_sugar list) corecs corec_defs =
  let
    fun mk_ctor_dtor_corec_thm dtor_inject dtor_ctor corec =
      iffD1 OF [dtor_inject, trans OF [corec, dtor_ctor RS sym]];

    val ctor_dtor_corec_thms =
      @{map 3} mk_ctor_dtor_corec_thm dtor_injects dtor_ctors dtor_corec_thms;

    val pre_map_defs = map map_def_of_mrbnf pre_mrbnfs;
    val live_nesting_map_ident0s = map map_ident0_of_mrbnf live_nesting_mrbnfs;

    val fp_b_names = map base_name_of_typ fpTs;

    val ctrss = map #ctrs ctr_sugars;
    val discss = map #discs ctr_sugars;
    val selsss = map #selss ctr_sugars;
    val disc_thmsss = map #disc_thmss ctr_sugars;
    val discIss = map #discIs ctr_sugars;
    val sel_thmsss = map #sel_thmss ctr_sugars;

    val coinduct_thms_pairs = derive_coinduct_thms_for_types ctxt true I pre_mrbnfs dtor_coinduct
      dtor_ctors live_nesting_mrbnfs fpTs Xs ctrXs_Tsss ns pre_abs_inverses abs_inverses mk_vimage2p
      ctr_defss ctr_sugars;

    fun mk_maybe_not pos = not pos ? HOLogic.mk_not;

    val gcorecs = map (lists_bmoc pgss) corecs;

    val corec_thmss =
      let
        val (us', _) = ctxt
          |> Variable.variant_fixes fp_b_names;

        val us = map2 (curry Free) us' fpTs;

        fun mk_goal c cps gcorec n k ctr m cfs' =
          fold_rev (fold_rev Logic.all) ([c] :: pgss)
            (Logic.list_implies (seq_conds (HOLogic.mk_Trueprop oo mk_maybe_not) n k cps,
               mk_Trueprop_eq (gcorec $ c, Term.list_comb (ctr, take m cfs'))));

        val mk_U = typ_subst_nonatomic (map2 (fn C => fn fpT => (mk_sumT (fpT, C), fpT)) Cs fpTs);

        fun tack (c, u) f =
          let val x' = Free (x, mk_sumT (fastype_of u, fastype_of c)) in
            Term.lambda x' (mk_case_sum (Term.lambda u u, Term.lambda c (f $ c)) $ x')
          end;

        fun build_corec cqg =
          let val T = fastype_of cqg in
            if exists_subtype_in Cs T then
              let
                val U = mk_U T;
                val build_simple =
                  indexify fst (map2 (curry mk_sumT) fpTs Cs)
                    (fn kk => fn _ => tack (nth cs kk, nth us kk) (nth gcorecs kk));
              in
                build_map ctxt [] [] build_simple (T, U) $ cqg
              end
            else
              cqg
          end;

        val cqgsss' = map (map (map build_corec)) cqgsss;
        val goalss = @{map 8} (@{map 4} oooo mk_goal) cs cpss gcorecs ns kss ctrss mss cqgsss';

        val tacss =
          @{map 4} (map ooo mk_corec_tac corec_defs live_nesting_map_ident0s)
            ctor_dtor_corec_thms pre_map_defs abs_inverses ctr_defss;

        fun prove goal tac =
          Goal.prove_sorry ctxt [] [] goal (tac o #context)
          |> Thm.close_derivation \<^here>;
      in
        map2 (map2 prove) goalss tacss
        |> map (map (unfold_thms ctxt @{thms case_sum_if}))
      end;

    val corec_disc_iff_thmss =
      let
        fun mk_goal c cps gcorec n k disc =
          mk_Trueprop_eq (disc $ (gcorec $ c),
            if n = 1 then \<^Const>\<open>True\<close>
            else Library.foldr1 HOLogic.mk_conj (seq_conds mk_maybe_not n k cps));

        val goalss = @{map 6} (map2 oooo mk_goal) cs cpss gcorecs ns kss discss;

        fun mk_case_split' cp = Thm.instantiate' [] [SOME (Thm.cterm_of ctxt cp)] @{thm case_split};

        val case_splitss' = map (map mk_case_split') cpss;

        val tacss = @{map 3} (map oo mk_corec_disc_iff_tac) case_splitss' corec_thmss disc_thmsss;

        fun prove goal tac =
          Variable.add_free_names ctxt goal []
          |> (fn vars => Goal.prove_sorry ctxt vars [] goal (tac o #context))
          |> Thm.close_derivation \<^here>;

        fun proves [_] [_] = []
          | proves goals tacs = map2 prove goals tacs;
      in
        map2 proves goalss tacss
      end;

    fun mk_corec_disc_thms corecs discIs = map (op RS) (corecs ~~ discIs);

    val corec_disc_thmss = map2 mk_corec_disc_thms corec_thmss discIss;

    fun mk_corec_sel_thm corec_thm sel sel_thm =
      let
        val (domT, ranT) = dest_funT (fastype_of sel);
        val arg_cong' =
          Thm.instantiate' (map (SOME o Thm.ctyp_of ctxt) [domT, ranT])
            [NONE, NONE, SOME (Thm.cterm_of ctxt sel)] arg_cong
          |> Thm.varifyT_global;
        val sel_thm' = sel_thm RSN (2, trans);
      in
        corec_thm RS arg_cong' RS sel_thm'
      end;

    fun mk_corec_sel_thms corec_thmss =
      @{map 3} (@{map 3} (map2 o mk_corec_sel_thm)) corec_thmss selsss sel_thmsss;

    val corec_sel_thmsss = mk_corec_sel_thms corec_thmss;
  in
    ((coinduct_thms_pairs,
      mk_coinduct_attrs fpTs (map #ctrs ctr_sugars) (map #discs ctr_sugars) mss),
     corec_thmss,
     corec_disc_thmss,
     (corec_disc_iff_thmss, simp_attrs),
     (corec_sel_thmsss, simp_attrs))
  end;

fun derive_rel_coinduct_thms_for_types ctxt nn fpA_Ts ns As Bs mss (ctr_sugars : ctr_sugar list)
    abs_inverses abs_injects ctor_injects dtor_ctors rel_pre_defs ctor_defss dtor_rel_coinduct
    live_nesting_rel_eqs =
  let
    val B_ify_T = Term.typ_subst_atomic (As ~~ Bs);
    val fpB_Ts = map B_ify_T fpA_Ts;

    val (Rs, IRs, fpAs, fpBs, _) =
      let
        val fp_names = map base_name_of_typ fpA_Ts;
        val ((((Rs, IRs), fpAs_names), fpBs_names), names_ctxt) = ctxt
          |> mk_Frees "R" (map2 mk_pred2T As Bs)
          ||>> mk_Frees "IR" (map2 mk_pred2T fpA_Ts fpB_Ts)
          ||>> Variable.variant_fixes fp_names
          ||>> Variable.variant_fixes (map (suffix "'") fp_names);
      in
        (Rs, IRs, map2 (curry Free) fpAs_names fpA_Ts, map2 (curry Free) fpBs_names fpB_Ts,
         names_ctxt)
      end;

    val ((discA_tss, selA_tsss), (discB_tss, selB_tsss)) =
      let
        val discss = map #discs ctr_sugars;
        val selsss = map #selss ctr_sugars;

        fun mk_discss ts Ts = map2 (map o rapp) ts (map (map (mk_disc_or_sel Ts)) discss);
        fun mk_selsss ts Ts =
          map2 (map o map o rapp) ts (map (map (map (mk_disc_or_sel Ts))) selsss);
      in
        ((mk_discss fpAs As, mk_selsss fpAs As),
         (mk_discss fpBs Bs, mk_selsss fpBs Bs))
      end;

    val prems =
      let
        fun mk_prem_ctr_concls n k discA_t selA_ts discB_t selB_ts =
          (if k = n then [] else [HOLogic.mk_eq (discA_t, discB_t)]) @
          (case (selA_ts, selB_ts) of
            ([], []) => []
          | (_ :: _, _ :: _) =>
            [Library.foldr HOLogic.mk_imp
              (if n = 1 then [] else [discA_t, discB_t],
               Library.foldr1 HOLogic.mk_conj
                 (map2 (build_rel_app ctxt (Rs @ IRs) fpA_Ts) selA_ts selB_ts))]);

        fun mk_prem_concl n discA_ts selA_tss discB_ts selB_tss =
          Library.foldr1 HOLogic.mk_conj (flat (@{map 5} (mk_prem_ctr_concls n)
            (1 upto n) discA_ts selA_tss discB_ts selB_tss))
          handle List.Empty => \<^term>\<open>True\<close>;

        fun mk_prem IR tA tB n discA_ts selA_tss discB_ts selB_tss =
          fold_rev Logic.all [tA, tB] (Logic.mk_implies (HOLogic.mk_Trueprop (IR $ tA $ tB),
            HOLogic.mk_Trueprop (mk_prem_concl n discA_ts selA_tss discB_ts selB_tss)));
      in
        @{map 8} mk_prem IRs fpAs fpBs ns discA_tss selA_tsss discB_tss selB_tsss
      end;

    val goal = HOLogic.mk_Trueprop (Library.foldr1 HOLogic.mk_conj (map2 mk_leq
      IRs (map2 (build_the_rel ctxt (Rs @ IRs) []) fpA_Ts fpB_Ts)));
    val vars = Variable.add_free_names ctxt goal [];

    val rel_coinduct0_thm =
      Goal.prove_sorry ctxt vars prems goal (fn {context = ctxt, prems} =>
        mk_rel_coinduct0_tac ctxt dtor_rel_coinduct (map (Thm.cterm_of ctxt) IRs) prems
          (map #exhaust ctr_sugars) (map (flat o #disc_thmss) ctr_sugars)
          (map (flat o #sel_thmss) ctr_sugars) ctor_defss dtor_ctors ctor_injects abs_injects
          rel_pre_defs abs_inverses live_nesting_rel_eqs)
      |> Thm.close_derivation \<^here>;
  in
    (postproc_co_induct ctxt nn @{thm predicate2D} @{thm predicate2D_conj} rel_coinduct0_thm,
     mk_coinduct_attrs fpA_Ts (map #ctrs ctr_sugars) (map #discs ctr_sugars) mss)
  end;

fun derive_set_induct_thms_for_types ctxt nn fpTs ctrss setss dtor_set_inducts exhausts set_pre_defs
    ctor_defs dtor_ctors Abs_pre_inverses =
  let
    fun mk_prems A Ps ctr_args t ctxt =
      (case fastype_of t of
        Type (type_name, innerTs) =>
        (case mrbnf_of ctxt type_name of
          NONE => ([], ctxt)
        | SOME mrbnf =>
          let
            fun seq_assm a set ctxt =
              let
                val X = HOLogic.dest_setT (range_type (fastype_of set));
                val (x, ctxt') = yield_singleton (mk_Frees "x") X ctxt;
                val assm = mk_Trueprop_mem (x, set $ a);
              in
                (case build_binary_fun_app Ps x a of
                  NONE =>
                  mk_prems A Ps ctr_args x ctxt'
                  |>> map (Logic.all x o Logic.mk_implies o pair assm)
                | SOME f =>
                  ([Logic.all x
                      (Logic.mk_implies (assm,
                         Logic.mk_implies (HOLogic.mk_Trueprop f,
                           HOLogic.mk_Trueprop (the (build_binary_fun_app Ps x ctr_args)))))],
                   ctxt'))
              end;
          in
            fold_map (seq_assm t o mk_set innerTs) (sets_of_mrbnf mrbnf) ctxt
            |>> flat
          end)
      | T =>
        if T = A then ([HOLogic.mk_Trueprop (the (build_binary_fun_app Ps t ctr_args))], ctxt)
        else ([], ctxt));

    fun mk_prems_for_ctr A Ps ctr ctxt =
      let
        val (args, ctxt') = mk_Frees "z" (binder_types (fastype_of ctr)) ctxt;
      in
        fold_map (mk_prems A Ps (list_comb (ctr, args))) args ctxt'
        |>> map (fold_rev Logic.all args) o flat
        |>> (fn prems => (prems, mk_names (length prems) (name_of_ctr ctr)))
      end;

    fun mk_prems_and_concl_for_type A Ps ((fpT, ctrs), set) ctxt =
      let
        val ((x, fp), ctxt') = ctxt
          |> yield_singleton (mk_Frees "x") A
          ||>> yield_singleton (mk_Frees "a") fpT;
        val concl = mk_Ball (set $ fp) (Term.absfree (dest_Free x)
          (the (build_binary_fun_app Ps x fp)));
      in
        fold_map (mk_prems_for_ctr A Ps) ctrs ctxt'
        |>> split_list
        |>> map_prod flat flat
        |>> apfst (rpair concl)
      end;

    fun mk_thm ctxt fpTs ctrss sets =
      let
        val A = HOLogic.dest_setT (range_type (fastype_of (hd sets)));
        val (Ps, ctxt') = mk_Frees "P" (map (fn fpT => A --> fpT --> HOLogic.boolT) fpTs) ctxt;
        val (((prems, concl), case_names), ctxt'') =
          fold_map (mk_prems_and_concl_for_type A Ps) (fpTs ~~ ctrss ~~ sets) ctxt'
          |>> apfst split_list o split_list
          |>> apfst (apfst flat)
          |>> apfst (apsnd (Library.foldr1 HOLogic.mk_conj))
          |>> apsnd flat;

        val vars = fold (Variable.add_free_names ctxt) (concl :: prems) [];
        val thm =
          Goal.prove_sorry ctxt vars prems (HOLogic.mk_Trueprop concl)
            (fn {context = ctxt, prems} =>
               mk_set_induct0_tac ctxt (map (Thm.cterm_of ctxt'') Ps) prems dtor_set_inducts
                 exhausts set_pre_defs ctor_defs dtor_ctors Abs_pre_inverses)
          |> Thm.close_derivation \<^here>;

        val case_names_attr = Attrib.case_names (quasi_unambiguous_case_names case_names);
        val induct_set_attrs = map (Attrib.internal o K o Induct.induct_pred o name_of_set) sets;
      in
        (thm, case_names_attr :: induct_set_attrs)
      end
    val consumes_attr = Attrib.consumes 1;
  in
    map (mk_thm ctxt fpTs ctrss
        #> nn = 1 ? map_prod (fn thm => rotate_prems ~1 (thm RS bspec)) (cons consumes_attr))
      (transpose setss)
  end;

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

    (* TODO: extract info from spec *)
    val var_typess = replicate (length ctrXs_repTs) []

    val (((pre_mrbnfs, absT_infos), _), (fp_res as {mrbnfs = fp_mrbnfs as any_fp_mrbnf :: _, ctors = ctors0,
             dtors = dtors0, xtor_co_recs = xtor_co_recs0, xtor_co_induct, dtor_ctors, ctor_dtors,
             ctor_injects, dtor_injects, xtor_maps, xtor_setss, xtor_rels, xtor_co_rec_thms,
             xtor_rel_co_induct, dtor_set_inducts, xtor_co_rec_transfers, xtor_co_rec_o_maps, ...},
           lthy)) =
      MRBNF_FP_Util.fixpoint_mrbnf false I (construct_fp mixfixes map_bs rel_bs pred_bs set_bss) fp_bs
        (map dest_TFree As) (map dest_TFree killed_As) (map dest_TFree Xs) ctrXs_repTs var_typess
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
            if is_some (mrbnf_of lthy bad_tc) orelse is_some (fp_sugar_of lthy bad_tc) then
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

    val fp_nesting_mrbnfs = nesting_mrbnfs lthy ctrXs_Tsss Xs;
    val live_nesting_mrbnfs = nesting_mrbnfs lthy ctrXs_Tsss As;

    val pre_map_defs = map map_def_of_mrbnf pre_mrbnfs;
    val pre_set_defss = map set_defs_of_mrbnf pre_mrbnfs;
    val pre_rel_defs = map rel_def_of_mrbnf pre_mrbnfs;
    val fp_nesting_set_maps = maps set_map_of_mrbnf fp_nesting_mrbnfs;
    val fp_nesting_rel_eq_onps = map rel_eq_onp_of_mrbnf fp_nesting_mrbnfs;
    val live_nesting_map_id0s = map map_id0_of_mrbnf live_nesting_mrbnfs;
    val live_nesting_map_ident0s = map map_ident0_of_mrbnf live_nesting_mrbnfs;
    val live_nesting_set_maps = maps set_map_of_mrbnf live_nesting_mrbnfs;
    val live_nesting_rel_eqs = map rel_eq_of_mrbnf live_nesting_mrbnfs;
    val live_nesting_rel_eq_onps = map rel_eq_onp_of_mrbnf live_nesting_mrbnfs;

    val liveness = liveness_of_fp_mrbnf num_As any_fp_mrbnf;
    val live = live_of_mrbnf any_fp_mrbnf;
    val bound = bound_of_mrbnf any_fp_mrbnf;
    val free = free_of_mrbnf any_fp_mrbnf;
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
           derive_map_set_rel_pred_thms plugins fp live bound free As Bs C E abs_inverses ctr_defs
             fp_nesting_set_maps fp_nesting_rel_eq_onps live_nesting_map_id0s live_nesting_set_maps
             live_nesting_rel_eqs live_nesting_rel_eq_onps [] fp_b_name fp_bnf fp_mrbnfs fpT ctor
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

          val maps0 = map map_of_mrbnf fp_mrbnfs;
          val f_names = variant_names num_As "f";
          val fs = map2 (curry Free) f_names (map (op -->) (As ~~ Bs));
          val live_gs = AList.find (op =) (fs ~~ liveness) true;

          val gmaps = map (fn map0 => Term.list_comb (mk_map live bound free As Bs map0, live_gs)) maps0;

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
          derive_induct_recs_thms_for_types plugins pre_mrbnfs recs_args_types xtor_co_induct
            xtor_co_rec_thms live_nesting_mrbnfs fp_nesting_mrbnfs fpTs Cs Xs ctrXs_Tsss abs_inverses
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
        |-> interpret_mrbnfs_register_fp_sugars plugins fpTs fpBTs Xs Least_FP pre_mrbnfs absT_infos
          fp_nesting_mrbnfs live_nesting_mrbnfs fp_res ctrXs_Tsss ctor_iff_dtors ctr_defss ctr_sugars
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

          val maps0 = map map_of_mrbnf fp_mrbnfs;
          val f_names = variant_names num_As "f";
          val fs = map2 (curry Free) f_names (map (op -->) (As ~~ Bs));
          val live_fs = AList.find (op =) (fs ~~ liveness) true;

          val fmaps = map (fn map0 => Term.list_comb (mk_map live bound free As Bs map0, live_fs)) maps0;

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
          derive_coinduct_corecs_thms_for_types lthy pre_mrbnfs (the corecs_args_types) xtor_co_induct
            dtor_injects dtor_ctors xtor_co_rec_thms live_nesting_mrbnfs fpTs Cs Xs ctrXs_Tsss kss mss
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
            (map (map (mk_set As)) (map sets_of_mrbnf fp_mrbnfs)) dtor_set_inducts
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
        |-> interpret_mrbnfs_register_fp_sugars plugins fpTs fpBTs Xs Greatest_FP pre_mrbnfs absT_infos
          fp_nesting_mrbnfs live_nesting_mrbnfs fp_res ctrXs_Tsss ctor_iff_dtors ctr_defss ctr_sugars
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
      |> live > 0 ? fold2 (fn Type (s, _) => fn bnf => register_mrbnf_raw s bnf) fpTs fp_mrbnfs
      |> @{fold_map 29} define_ctrs_dtrs_for_type_etc fp_mrbnfs fp_bs fpTs Cs Es ctors dtors
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