theory Composition
  imports "thys/MRBNF_Composition"
begin

ML \<open>
Multithreading.parallel_proofs := 1;
\<close>

datatype \<kappa> =
  Star ("\<star>")
  | KArrow \<kappa> \<kappa> (infixr "\<rightarrow>" 50)

(*
  TyVar 'tyvar
  | TyArrow
  | TyApp 'd 'd
  | TyForall 'btyvar \<kappa> 'c
*)
ML \<open>
val systemf_type = @{typ "'tyvar + unit + 'd * 'd + 'btyvar * \<kappa> * 'c"}
val systemf_type_vars = {
  lives = [("''d", @{sort type}), ("'c", @{sort type})],
  frees = [("'tyvar", @{sort type})],
  bounds = [("'btyvar", @{sort type})],
  deads = []
}
\<close>

declare [[bnf_internals]]
datatype (setF1_F: 'a, setF2_F: 'a', setL3_F: 'x, setB4_F: 'b, setB5_F: 'b', setL6_F: 'c, setL7_F: 'd, setL8_F: 'e, setL9_F: 'f) F_raw =
  E "'x + 'a + ('a' * 'b') * 'c * 'd + 'a' * 'f"
  for map: map_F rel: rel_F
type_synonym ('a, 'a', 'x, 'b, 'b', 'c, 'd, 'e, 'f) F = "('a, 'a', 'x, 'b, 'b', 'c, 'd, 'e, 'f) F_raw"

datatype (setF1_F': 'a, setF2_F': 'a', setL3_F': 'x, setB4_F': 'b, setB5_F': 'b', setL6_F': 'c, setL7_F': 'd, setL8_F': 'e, setL9_F': 'f) F_raw' =
  E "'x + 'a + ('a' * 'b') * 'c * 'd + 'a' * 'f"
  for map: map_F' rel: rel_F'
type_synonym ('a, 'a', 'x, 'b, 'b', 'c, 'd, 'e, 'f) F' = "('a, 'a', 'x, 'b, 'b', 'c, 'd, 'e, 'f) F_raw'"

datatype (setF1_G: 'a, setF2_G: 'a', setL3_G: 'y, setB4_G: 'b, setB5_G: 'b', setL6_G: 'g, setL7_G: 'h) G_raw =
  E "'y + 'a + ('a' * 'b') * 'y * 'g + 'a' * 'g * 'h"
  for map: map_G rel: rel_G
type_synonym ('a, 'a', 'y, 'b, 'b', 'g, 'h) G = "('a, 'a', 'y, 'b, 'b', 'g, 'h) G_raw"

print_mrbnfs
print_bnfs

local_setup \<open>snd o the o MRBNF_Def.as_mrbnf "Sum_Type.sum"\<close>
local_setup \<open>snd o the o MRBNF_Def.as_mrbnf "List.list"\<close>
print_mrbnfs

declare [[quick_and_dirty=true]]
mrbnf F: "('a, 'a', 'x, 'b, 'b', 'c, 'd, 'e, 'f) F"
  map: "map_F"
  sets:
   free: "setF1_F :: _ \<Rightarrow> 'a set"
   free: "setF2_F :: _ \<Rightarrow> 'a' set"
   live: "setL3_F :: _ \<Rightarrow> 'x set"
   bound: "setB4_F :: _ \<Rightarrow> 'b set"
   bound: "setB5_F :: _ \<Rightarrow> 'b' set"
   live: "setL6_F :: _ \<Rightarrow> 'c set"
   live: "setL7_F :: _ \<Rightarrow> 'd set"
   live: "setL8_F :: _ \<Rightarrow> 'e set"
   live: "setL9_F :: _ \<Rightarrow> 'f set"
  bd: "natLeq"
  wits: "F_raw.E o Inl"
  rel: "\<lambda>X. rel_F (=) (=) X (=) (=)"
  pred: "\<lambda>X. pred_F_raw (\<lambda>_. True) (\<lambda>_. True) X (\<lambda>_. True) (\<lambda>_. True)"
  sorry

mrbnf F': "('a, 'a', 'x, 'b, 'b', 'c, 'd, 'e, 'f) F'"
  map: "map_F'"
  sets:
   bound: "setF1_F' :: _ \<Rightarrow> 'a set"
   bound: "setF2_F' :: _ \<Rightarrow> 'a' set"
   live: "setL3_F' :: _ \<Rightarrow> 'x set"
   free: "setB4_F' :: _ \<Rightarrow> 'b set"
   free: "setB5_F' :: _ \<Rightarrow> 'b' set"
   live: "setL6_F' :: _ \<Rightarrow> 'c set"
   live: "setL7_F' :: _ \<Rightarrow> 'd set"
   live: "setL8_F' :: _ \<Rightarrow> 'e set"
   live: "setL9_F' :: _ \<Rightarrow> 'f set"
  bd: "card_suc natLeq"
  wits: "F_raw'.E o Inl"
  rel: "\<lambda>X. rel_F' (=) (=) X (=) (=)"
  pred: "\<lambda>X. pred_F_raw' (\<lambda>_. True) (\<lambda>_. True) X (\<lambda>_. True) (\<lambda>_. True)"
  sorry

mrbnf G: "('a, 'a', 'y, 'b, 'b', 'g, 'h) G_raw"
  map: "map_G"
  sets:
    free: "setF1_G :: _ \<Rightarrow> 'a set"
    free: "setF2_G :: _ \<Rightarrow> 'a' set"
    live: "setL3_G :: _ \<Rightarrow> 'y set"
    bound: "setB4_G :: _ \<Rightarrow> 'b set"
    bound: "setB5_G :: _ \<Rightarrow> 'b' set"
    live: "setL6_G :: _ \<Rightarrow> 'g set"
    live: "setL7_G :: _ \<Rightarrow> 'h set"
  bd: "natLeq"
  wits: "G_raw.E o Inl"
  rel: "\<lambda>X. rel_G (=) (=) X (=) (=)"
  pred: "\<lambda>X. pred_G_raw (\<lambda>_. True) (\<lambda>_. True) X (\<lambda>_. True) (\<lambda>_. True)"
  sorry
declare [[quick_and_dirty=false]]

print_mrbnfs

ML \<open>
val sum = the (MRBNF_Def.mrbnf_of @{context} \<^type_name>\<open>sum\<close>)
val list = the (MRBNF_Def.mrbnf_of @{context} \<^type_name>\<open>list\<close>)
val f = the (MRBNF_Def.mrbnf_of @{context} "Composition.F")
val f' = the (MRBNF_Def.mrbnf_of @{context} "Composition.F'")
val g = the (MRBNF_Def.mrbnf_of @{context} "Composition.G")
\<close>

declare [[goals_limit = 50]]
declare [[ML_print_depth=10000]]


ML_file \<open>./Tools/mrbnf_comp_tactics.ML\<close>
ML_file \<open>./Tools/mrbnf_comp.ML\<close>

ML \<open>
Multithreading.parallel_proofs := 0;
\<close>

local_setup \<open>fn lthy =>
  let
    val name = Long_Name.base_name \<^type_name>\<open>sum\<close>
    fun qualify i =
              let val namei = name ^ BNF_Util.nonzero_string_of_int i;
              in Binding.qualify true namei end
    val Xs = []
    val resBs = [dest_TFree @{typ 'a}]
    fun flatten_tyargs Ass =
      subtract (op =) Xs (filter (fn T => exists (fn Ts => member (op =) Ts T) Ass) resBs) @ Xs;
  val ((mrbnf, tys), (_, lthy')) = (MRBNF_Comp.compose_mrbnf MRBNF_Def.Do_Inline qualify flatten_tyargs
        sum [list, MRBNF_Comp.ID_mrbnf] [] [[], []] [[@{typ 'a}], [@{typ 'a}]] ((MRBNF_Comp.empty_comp_cache, MRBNF_Comp.empty_unfolds), lthy))
  val _ = @{print} mrbnf
  val _ = @{print} tys
  in lthy'
  end\<close>

local_setup \<open>fn lthy =>
  let
    val name = Long_Name.base_name "Composition.G"
    fun qualify i =
              let val namei = name ^ BNF_Util.nonzero_string_of_int i;
              in Binding.qualify true namei end
    val Xs = []
    val Ts = [@{typ 'a}, @{typ 'b}, @{typ 'c}, @{typ 'd}, @{typ 'e}, @{typ 'f}, @{typ 'g}, @{typ 'h}, @{typ 'i}]
    val Ts' = [@{typ 'd}, @{typ 'e}, @{typ 'c}, @{typ 'b}, @{typ 'a}, @{typ 'f}, @{typ 'g}, @{typ 'i}, @{typ 'h}]
    val resBs = map dest_TFree Ts
    fun flatten_tyargs Ass =
      subtract (op =) Xs (filter (fn T => exists (fn Ts => member (op =) Ts T) Ass) resBs) @ Xs;
  val ((mrbnf, tys), (_, lthy')) = (MRBNF_Comp.compose_mrbnf MRBNF_Def.Do_Inline qualify flatten_tyargs
        g [f, f', f] [] [[], [], []] [Ts, Ts', Ts] ((MRBNF_Comp.empty_comp_cache, MRBNF_Comp.empty_unfolds), lthy))
  val _ = @{print} tys
  val _ = @{print} mrbnf
  in lthy'
  end\<close>

ML \<open>
val test = @{typ "unit + unit + 'a list"}
\<close>

(*local_setup \<open>snd o MRBNF_Comp.mrbnf_of_typ { lives = [("'a", @{sort type})], frees = [], bounds = [], deads = [] } test\<close>

print_mrbnfs*)

end
