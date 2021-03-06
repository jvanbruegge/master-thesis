theory Composition
  imports "thys/MRBNF_Composition"
begin

datatype \<kappa> =
  Star ("\<star>")
  | KArrow \<kappa> \<kappa> (infixr "\<rightarrow>" 50)

(*
binder_datatype 'var \<tau> =
  | TyVar 'var
  | TyArrow
  | TyApp "'var \<tau>" "'var \<tau>"
  | TyForall a::"'var" \<kappa> t::"'var \<tau>" binds a in t

  \<down>

binder_datatype ('tyvar, 'btyvar, 'rec, 'body) \<tau>_pre =
    TyVar 'tyvar
  | TyArrow
  | TyApp 'rec 'rec
  | TyForall 'btyvar \<kappa> 'body
*)
local_setup \<open>fn lthy =>
let
  val systemf_type_name = "\<tau>_pre"
  val systemf_type = @{typ "'tyvar + unit + 'rec * 'rec + 'btyvar * \<kappa> * 'body"}
  val Xs = []
  val resBs = map dest_TFree [@{typ 'tyvar}, @{typ 'btyvar}, @{typ 'body}, @{typ 'rec}]
  fun flatten_tyargs Ass = subtract (op =) Xs (filter (fn T => exists (fn Ts => member (op =) Ts T) Ass) resBs) @ Xs;
  val qualify = Binding.prefix_name (systemf_type_name ^ "_")

  val ((mrbnf, tys), (accum, lthy')) = MRBNF_Comp.mrbnf_of_typ false MRBNF_Def.Smart_Inline qualify flatten_tyargs Xs []
    [(dest_TFree @{typ 'tyvar}, MRBNF_Def.Free_Var), (dest_TFree @{typ 'btyvar}, MRBNF_Def.Bound_Var)] systemf_type
    ((MRBNF_Comp.empty_comp_cache, MRBNF_Comp.empty_unfolds), lthy)
  val ((mrbnf, (Ds, info)), lthy'') = MRBNF_Comp.seal_mrbnf I (snd accum) (Binding.name systemf_type_name) true (fst tys) [] mrbnf lthy'
in lthy'' end
\<close>
(*
binder_datatype ('var, 'tyvar) "term" =
    Var 'var
  | App "('var, 'tyvar) term" "('var, 'tyvar) term"
  | TApp "('var, 'tyvar) term" "'tyvar \<tau>"
  | Lam x::"'var" "'tyvar \<tau>" t::"('var, 'tyvar) term" binds x in t
  | TyLam a::"'btyvar" \<kappa> t::"('var, 'tyvar) term" binds a in t
  | Let "(xs::'var * 'tyvar \<tau> * ('var, 'tyvar) term) list" t::"('var, 'tyvar) term" binds xs in t
  | LetRec "(xs::'var * 'tyvar \<tau> * ts::('var, 'tyvar) term) list" t::"('var, 'tyvar) term" binds xs in t ts

  \<down>*                  (normally the \<tau> type would not be expanded, would be recursive already)

binder_datatype ('var, 'bvar, 'rec, 'body, 'tyvar, 'btyvar, 'trec, 'tbody) "term_pre" =
    Var 'var
  | App 'rec 'rec
  | TApp 'rec "('tyvar, 'btyvar, 'trec, 'tbody) \<tau>_pre"
  | Lam 'bvar "('tyvar, 'btyvar, 'trec, 'tbody) \<tau>_pre" 'body
  | TyLam 'btyvar \<kappa> 'body
  | Let "('bvar * ('tyvar, 'btyvar, 'trec, 'tbody) \<tau>_pre * 'rec) list" 'body
  | LetRec "('bvar * ('tyvar, 'btyvar, 'trec, 'tbody) \<tau>_pre * 'body) list" 'body
*)
local_setup \<open>fn lthy =>
let
  val systemf_term_name = "term_pre"
  val systemf_term = @{typ "'var + 'rec * 'rec + 'rec * ('tyvar, 'btyvar, 'trec, 'tbody) \<tau>_pre +
    'bvar * ('tyvar, 'btyvar, 'trec, 'tbody) \<tau>_pre * 'body + 'btyvar * \<kappa> * 'body +
    ('bvar * ('tyvar, 'btyvar, 'trec, 'tbody) \<tau>_pre * 'rec) list * 'body +
    ('bvar * ('tyvar, 'btyvar, 'trec, 'tbody) \<tau>_pre * 'body) list * 'body"}
  val Xs = []
  val resBs = map dest_TFree [@{typ 'var}, @{typ 'bvar}, @{typ 'body}, @{typ 'rec}, @{typ 'tyvar}, @{typ 'btyvar}, @{typ 'trec}, @{typ 'tbody}]
  fun flatten_tyargs Ass = subtract (op =) Xs (filter (fn T => exists (fn Ts => member (op =) Ts T) Ass) resBs) @ Xs;
  val qualify = Binding.prefix_name (systemf_term_name ^ "_")

  val ((mrbnf, tys), (accum, lthy')) = MRBNF_Comp.mrbnf_of_typ false MRBNF_Def.Smart_Inline qualify flatten_tyargs Xs []
    [(dest_TFree @{typ 'var}, MRBNF_Def.Free_Var), (dest_TFree @{typ 'bvar}, MRBNF_Def.Bound_Var)] systemf_term
    ((MRBNF_Comp.empty_comp_cache, MRBNF_Comp.empty_unfolds), lthy)
  val ((mrbnf, (Ds, info)), lthy'') = MRBNF_Comp.seal_mrbnf I (snd accum) (Binding.name systemf_term_name) true (fst tys) [] mrbnf lthy'
  val _ = @{print} tys
  val _ = @{print} info
  val _ = @{print} mrbnf
in lthy'' end
\<close>

print_theorems

end
