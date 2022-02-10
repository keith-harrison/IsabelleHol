theory Tree1
imports Main Block Variables "HOL-Library.Tree"
begin

fun correct_block :: "Block \<Rightarrow> bool" where
"correct_block bl = (if (bid bl = sl bl)  then True else False)"

fun correct_blocks :: "Chain \<Rightarrow> bool" where
"correct_blocks [] = True"|
"correct_blocks (c#cs) = (if correct_block c then correct_blocks cs else False)"
