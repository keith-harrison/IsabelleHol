theory Blockchain2
  imports Main "HOL-Library.Tree"
begin
type_synonym Transactions = nat

type_synonym Party = nat
type_synonym Slot = nat

(*type_synonym Hash = "nat list"*)
datatype Hash = H nat nat
definition "Slotzero = 0"
type_synonym Delay = nat
type_synonym Parties = "Party list"
 
fun Winner :: "Party \<Rightarrow> Slot \<Rightarrow> bool" where
"Winner P S = (if P = S then True else False)"

(*"Hash option"*)
record Block =
  sl :: Slot
  txs :: Transactions
  pred :: Hash
  bid :: Party

type_synonym Chain = "Block list"
type_synonym Chains = "Chain list"
type_synonym BlockPool = "Block list"



fun HashCompare' :: "Hash \<Rightarrow> Block \<Rightarrow> bool" where
"HashCompare' (H a b) bl1 = ((a = sl bl1) \<and> (b = bid bl1))"


fun HashCompare :: "Block \<Rightarrow> Block \<Rightarrow> bool" where
"HashCompare bl1 bl2 = HashCompare' (pred bl2) bl1"

definition "GenBlock = \<lparr>sl = 0, txs = 0, pred = H 0 0 ,bid = 0\<rparr>"
definition "Block1 = \<lparr>sl = 1, txs =1, pred = H 0 0, bid = 1\<rparr>"
definition "Block2 = \<lparr> sl = 2, txs = 0, pred = H 1 1, bid = 1\<rparr>"
definition "Block3 = \<lparr> sl = 3, txs = 0, pred = H 2 1, bid = 1\<rparr>"

value "HashCompare GenBlock Block1"
value "HashCompare Block1 Block2"
value "HashCompare Block2 Block3"
value "HashCompare GenBlock Block2"
value "HashCompare Block2 Block1"
value "HashCompare Block1 GenBlock"

fun valid_blocks ::"Block \<Rightarrow> Block \<Rightarrow> bool" where
"valid_blocks b1 b2 =  (HashCompare b2 b1 \<and> (sl b2 < sl b1)) "

value "valid_blocks Block1 GenBlock"
value "valid_blocks Block2 Block1"
value "valid_blocks Block3 Block2"
value "valid_blocks Block2 Block3"
value "b#[c]"

(*checking for b's being a node only and a /genesis node at the end of the list missing*)
fun valid_chain :: "Chain \<Rightarrow> bool" where
"valid_chain [] = False"|
"valid_chain [b1] = (if b1 = GenBlock then True else False)"|
"valid_chain (b1#b2#c) = (if valid_blocks b1 b2 \<and> (b1 \<noteq> GenBlock) then valid_chain (b2#c) else False)"

value "valid_chain [Block3,Block2,Block1,GenBlock]"
value "valid_chain [\<lparr>sl = 0, txs = 0, pred = H 0 0, bid = 0\<rparr>, \<lparr>sl = 0, txs = 0, pred = H 0 0, bid = 0\<rparr>, \<lparr>sl = 0, txs = 0, pred = H 0 0, bid = 0\<rparr>]"
value "HashCompare  \<lparr>sl = 1, txs = 1, pred = H 0 0, bid = 1\<rparr> \<lparr>sl = 2, txs = 1, pred = H 1 1, bid = 2\<rparr>"


 
datatype T = Leaf | Node Block T T 

fun allBlocks :: "T \<Rightarrow> BlockPool" where 
"allBlocks (Node m l r) = allBlocks l @ allBlocks r @ [m]"|
"allBlocks Leaf = []"

(*
fun allBlocksGen :: "T \<Rightarrow> BlockPool" where
"allBlocksGen (Node m l r) = (if m = GenBlock then allBlocks l@allBlocks r @[m]else [])"|
"allBlocksGen Leaf = []"
*)

fun allBlocksAppend :: "Block \<Rightarrow>BlockPool list\<Rightarrow> BlockPool list" where
"allBlocksAppend Bl BlP = (map (\<lambda> bl. bl @ [Bl]) BlP)"

fun allBlocks' :: "T \<Rightarrow> BlockPool list" where
"allBlocks' (Node m l r) = allBlocksAppend m (allBlocks' l) @allBlocksAppend m (allBlocks' r)"|
"allBlocks' Leaf = [[]]"
(*
fun allBlocksGen' :: "T \<Rightarrow> BlockPool list" where
"allBlocksGen' (Node m l r) = (if m = GenBlock then allBlocksAppend m (allBlocks' l) @allBlocksAppend m (allBlocks' r) else [])"
*)
definition "tree0 = Node GenBlock Leaf Leaf"

lemma initialTree : "allBlocks tree0 = [GenBlock]" 
  by (simp add: GenBlock_def tree0_def)

fun extendTree :: "T \<Rightarrow> Block \<Rightarrow> T" where
"extendTree (Node Bl1 Leaf Leaf) Bl2 =  (if valid_blocks Bl2 Bl1 then (Node Bl1 (Node Bl2 Leaf Leaf) Leaf) else (Node Bl1 Leaf Leaf)) "|
"extendTree (Node Bl1 t1 Leaf) Bl2 =  (if valid_blocks Bl2 Bl1 then (Node Bl1 t1 (Node Bl2 Leaf Leaf)) else (Node Bl1 (extendTree t1 Bl2) Leaf))"|
"extendTree (Node Bl1 Leaf t1) Bl2 =  (if valid_blocks Bl2 Bl1 then (Node Bl1 (Node Bl2 Leaf Leaf) t1) else (Node Bl1  Leaf (extendTree t1 Bl2)))"|
"extendTree (Node Bl1 t1 t2) Bl2 =(Node Bl1 (extendTree t1 Bl2) (extendTree t2 Bl2))"|
"extendTree Leaf Bl2 = Leaf"
value "valid_blocks Block1 GenBlock"
value "valid_chain [Block1,GenBlock]"
value "Block1 # [GenBlock]"


lemma "extendTree Leaf B = Leaf"
  by simp 


value "(extendTree tree0 Block1) = (Node GenBlock (Node Block1 Leaf Leaf)  Leaf)"
value "extendTree (T.Node \<lparr>sl = 0, txs = 0, pred = H 0 0, bid = 0\<rparr> T.Leaf (T.Node \<lparr>sl = 1, txs = 0, pred = H 0 0, bid = 0\<rparr> T.Leaf T.Leaf))  \<lparr>sl =1 , txs = 0, pred = H 0 0, bid = 0\<rparr> "
value "valid_chain  (\<lparr>sl = 0, txs = 0, pred = H 0 0, bid = 0\<rparr>#[\<lparr>sl = 0, txs = 0, pred = H 0 0, bid = 1\<rparr>])"
lemma ExtendInitial : "(extendTree tree0 Block1) = (Node GenBlock (Node Block1 Leaf Leaf) Leaf)"
  by (simp add: GenBlock_def tree0_def Block1_def)

definition valid_t where
"valid_t t = (\<forall>c\<in>set(allBlocks' t).valid_chain c)"

lemma BaseExtend : "(extendTree t b \<noteq> t) \<Longrightarrow> set (allBlocks (extendTree t b)) =set ([b]@ allBlocks t)"
proof(induction "t")
  case Leaf
  then show ?case 
    by simp
next
  case (Node x1 t1 t2) note Nodex1 = this
  then show ?case proof (cases "t1")
    case Leaf note Leaft1 = this
    then show ?thesis proof (cases "t2")
      case Leaf
      then show ?thesis using Nodex1 Leaft1 
        by auto
    next
      case (Node x21 x22 x23)
      then show ?thesis using Nodex1 Leaft1
        by auto
    qed
  next
    case (Node x21 x22 x23) note Nodet1 = this
    then show ?thesis proof (cases "t2")
      case Leaf
      then show ?thesis using Nodex1 Nodet1 
        by auto
    next
      case (Node x21 x22 x23)
      then show ?thesis using Nodex1 Nodet1 
        by fastforce
    qed
  qed
qed

lemma GenExtend : assumes "(extendTree t b \<noteq> t)\<and>valid_t t" shows "set (allBlocks (extendTree t b)) =set ([b]@ allBlocks t)"
proof(cases "t")
  case Leaf note LeafCase = this
  then show ?thesis using assms LeafCase
    by simp
next
  case (Node x1 t1 t2)
  then show ?thesis proof(cases "t1")
    case Leaf
    then show ?thesis using assms BaseExtend 
      by simp
  next
    case (Node x1 t11 t12)
    then show ?thesis using assms BaseExtend
      by simp
  qed
qed


fun best_c :: "nat \<Rightarrow> Block list list \<Rightarrow> (Block list \<times> nat \<times> bool) option"where 
"best_c slot list = (let list' = map (\<lambda> l. (l,sl (hd l), valid_chain l)) list in find (\<lambda> (c,s,v).v\<and>(s\<le>slot)) list')"

fun get_first :: "(Block list \<times> nat \<times> bool) option \<Rightarrow>Block list" where
"get_first a = (case a of None \<Rightarrow> [] | Some a \<Rightarrow> fst a)"

lemma best_c_none : "best_c n [] = None"
  by(simp)


lemma find_in : \<open>find p ls = Some l\<Longrightarrow> l\<in> set(ls)\<close>
proof(induction ls)
  case Nil
  then show ?case by simp
next
  case (Cons a ls)
  then show ?case
    by (metis find_Some_iff nth_mem)
qed

lemma best_c_in : "best_c n bl \<noteq> None \<Longrightarrow> get_first(best_c n bl) \<in> set(bl)"
  apply(simp add: find_in)
proof(induction bl)
  case Nil
  then show ?case
    by simp 
next
  case (Cons a bl)
  then show ?case
    by auto
qed 
value "valid_chain [\<lparr>sl = 2, txs = 2, pred = H 1 1, bid = 2\<rparr>, \<lparr>sl = 1, txs = 1, pred = H 0 0, bid = 1\<rparr>, \<lparr>sl = 0, txs = 0, pred = H 0 0, bid = 0\<rparr>]"

value "best_c (3::nat) (allBlocks'((Node GenBlock (Node \<lparr>sl = 1, txs = 1, pred = H 0 0, bid = 1\<rparr> (Node \<lparr>sl = 2, txs = 2, pred = H 1 1, bid = 2\<rparr> Leaf Leaf) Leaf)
 (Node \<lparr>sl = 2, txs = 2, pred = H 1 1, bid = 2\<rparr> Leaf Leaf))) )"


fun best_chain :: "Slot \<Rightarrow> T \<Rightarrow> Block list" where
"best_chain s Leaf = []"|
"best_chain s (Node x l r) = get_first ( best_c s (allBlocks' (Node x l r)))"
value "best_chain 10  ((Node GenBlock (Node \<lparr>sl = 1, txs = 1, pred = H 0 0, bid = 1\<rparr> (Node \<lparr>sl = 2, txs = 2, pred = H 1 1, bid = 2\<rparr> Leaf Leaf) Leaf)
 (Node \<lparr>sl = 2, txs = 2, pred = H 1 1, bid = 2\<rparr> Leaf Leaf)))"
value "best_c (3::nat) (allBlocks' ((Node GenBlock (Node \<lparr>sl = 1, txs = 1, pred = H 0 0, bid = 1\<rparr>  Leaf Leaf)
 (Node \<lparr>sl = 1, txs = 1, pred = H 0 0, bid = 2\<rparr> Leaf Leaf))))"

value "allBlocks' ((Node GenBlock (Node \<lparr>sl = 1, txs = 1, pred = H 0 0, bid = 1\<rparr> (Node \<lparr>sl = 2, txs = 2, pred = H 1 1, bid = 2\<rparr> Leaf Leaf) Leaf)
 (Node \<lparr>sl = 2, txs = 2, pred = H 1 1, bid = 2\<rparr> Leaf Leaf)))"

value "valid_chain (best_chain 0 (Node GenBlock (Node \<lparr>sl = 1, txs = 1, pred = H 0 0, bid = 1\<rparr> (Node \<lparr>sl = 1, txs = 1, pred = H 1 1, bid = 1\<rparr> (Node \<lparr>sl = 2, txs = 2, pred = H 1 1, bid = 2\<rparr> Leaf Leaf) Leaf) Leaf)
 (Node \<lparr>sl = 1, txs = 1, pred = H 1 1, bid = 1\<rparr> Leaf Leaf)))"

value "best_chain 2  ((Node GenBlock (Node \<lparr>sl = 1, txs = 1, pred = H 0 0, bid = 1\<rparr> (Node \<lparr>sl = 1, txs = 1, pred = H 1 1, bid = 1\<rparr> Leaf Leaf) Leaf)
 (Node \<lparr>sl = 1, txs = 1, pred = H 1 1, bid = 1\<rparr> Leaf Leaf)))"
value "allBlocks'  (Node \<lparr>sl = 0, txs = 0, pred = H 0 0, bid = 1\<rparr> Leaf Leaf)"

value "valid_chain (best_chain 1 (T.Node \<lparr>sl = 0, txs = 0, pred = H 0 0, bid = 0\<rparr> T.Leaf T.Leaf))"

lemma base_best_valid:assumes "s>0" shows "(valid_chain(best_chain s tree0) = True)"
  using assms apply(simp add: GenBlock_def best_c_in tree0_def) done

lemma best_valid :assumes"t\<noteq>Leaf\<and>(s >0) \<and>valid_t t" shows "valid_chain (best_chain s t)"
proof(cases "t")
  case Leaf
  then show ?thesis using assms
    by simp
next
  case (Node x21 x22 x23) note Nodet = this
  then show ?thesis proof(cases "x22")
    case Leaf note Leafx22 = this
    then show ?thesis proof(cases"x23")
      case Leaf
      then show ?thesis using assms Nodet Leafx22 apply(simp add:GenBlock_def valid_t_def base_best_valid) apply(auto) apply(metis) done
    next
      case (Node x211 x221 x231)
      then show ?thesis using assms Nodet Leafx22 apply(simp add:GenBlock_def valid_t_def base_best_valid) apply(auto)  done
    qed
  next
    case (Node x211 x221 x231) note Nodex22 = this
    then show ?thesis proof(cases"x23")
      case Leaf note Leafx23 = this
      then show ?thesis  proof(cases"rec_list Map.empty (\<lambda>x xs xsa P. if P x then Some x else xsa P)
               (map (\<lambda>l. (l, Record.iso_tuple_fst Record.tuple_iso_tuple
                              (Record.iso_tuple_fst Record.tuple_iso_tuple (Record.iso_tuple_fst Block_ext_Tuple_Iso (case l of x21 # x22 \<Rightarrow> x21))),
                          valid_chain l))
                 (rec_list (\<lambda>ys. ys) (\<lambda>x xs xsa ys. x # xsa ys)
                   (map (\<lambda>bl. rec_list (\<lambda>ys. ys) (\<lambda>x xs xsa ys. x # xsa ys) bl [x21])
                     (rec_list (\<lambda>ys. ys) (\<lambda>x xs xsa ys. x # xsa ys) (map (\<lambda>bl. rec_list (\<lambda>ys. ys) (\<lambda>x xs xsa ys. x # xsa ys) bl [x211]) (allBlocks' x221))
                       (map (\<lambda>bl. rec_list (\<lambda>ys. ys) (\<lambda>x xs xsa ys. x # xsa ys) bl [x211]) (allBlocks' x231))))
                   [[x21]]))
               (\<lambda>(c, sa, v). v \<and> sa \<le> s) = None")
        case True
        then show ?thesis using assms Nodet Nodex22 Leafx23
       apply(simp add:GenBlock_def valid_t_def base_best_valid best_c_in tree0_def map_def append_def sl_def hd_def set_def find_def Let_def o_def fst_def) apply(auto)
          sorry
      next
        case False
        then show ?thesis using assms Nodet Nodex22 Leafx23
          apply(simp add:GenBlock_def valid_t_def base_best_valid best_c_in tree0_def map_def append_def sl_def hd_def set_def find_def Let_def o_def fst_def) apply(auto)
          sorry
      qed
    next
      case (Node x212 x222 x232) note Nodex23 = this
      then show ?thesis proof(cases"rec_list Map.empty (\<lambda>x xs xsa P. if P x then Some x else xsa P)
            (map (\<lambda>l. (l, Record.iso_tuple_fst Record.tuple_iso_tuple
                           (Record.iso_tuple_fst Record.tuple_iso_tuple (Record.iso_tuple_fst Block_ext_Tuple_Iso (case l of x21 # x22 \<Rightarrow> x21))),
                       valid_chain l))
              (rec_list (\<lambda>ys. ys) (\<lambda>x xs xsa ys. x # xsa ys)
                (map (\<lambda>bl. rec_list (\<lambda>ys. ys) (\<lambda>x xs xsa ys. x # xsa ys) bl [x21])
                  (rec_list (\<lambda>ys. ys) (\<lambda>x xs xsa ys. x # xsa ys) (map (\<lambda>bl. rec_list (\<lambda>ys. ys) (\<lambda>x xs xsa ys. x # xsa ys) bl [x211]) (allBlocks' x221))
                    (map (\<lambda>bl. rec_list (\<lambda>ys. ys) (\<lambda>x xs xsa ys. x # xsa ys) bl [x211]) (allBlocks' x231))))
                (map (\<lambda>bl. rec_list (\<lambda>ys. ys) (\<lambda>x xs xsa ys. x # xsa ys) bl [x21])
                  (rec_list (\<lambda>ys. ys) (\<lambda>x xs xsa ys. x # xsa ys) (map (\<lambda>bl. rec_list (\<lambda>ys. ys) (\<lambda>x xs xsa ys. x # xsa ys) bl [x212]) (allBlocks' x222))
                    (map (\<lambda>bl. rec_list (\<lambda>ys. ys) (\<lambda>x xs xsa ys. x # xsa ys) bl [x212]) (allBlocks' x232))))))
            (\<lambda>(c, sa, v). v \<and> sa \<le> s) =
      None")
        case True
        then show ?thesis using assms Nodet Nodex22 Nodex23 apply(simp add:GenBlock_def valid_t_def base_best_valid best_c_in tree0_def map_def append_def sl_def hd_def set_def find_def Let_def o_def fst_def) apply(auto) sorry

      next
        case False
        then show ?thesis using assms Nodet Nodex22 Nodex23 apply(simp add:GenBlock_def valid_t_def base_best_valid best_c_in tree0_def map_def append_def sl_def hd_def set_def find_def Let_def o_def fst_def) apply(auto) sorry

      qed
      
      qed
  qed
qed
