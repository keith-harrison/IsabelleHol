theory LocalState
  imports Main Variables Block Tree
begin

(* LocalState
 This file defines the LocalState 
a party should maintain.*)
record LocalState =
      tT :: treeType (* tree type*) 
      pk :: Party
      tree :: tT

(*can make an instance like below
definition LocalStateSettable :: LocalState where
"LocalStateSettable = \<lparr>tT = tT,pk=pk,tree = tree\<rparr>"
*)
end