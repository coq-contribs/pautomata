Require Import PAutoMod.
Extract Constant Time => "int".   
Extract Constant T0 => "0".        
Extract Constant T1 => "1".    
Extract Constant Tmult => "( * )".
Extract Constant Tminus => "(-)".
Extract Constant Tplus => "(+)".
Extract Constant Topp => "(fun x -> -x)".
Extract Constant total_order =>
 "(fun r1 r2 -> if r1 < r2 then Coq_inleft Coq_left 
                 else if r1 = r2 then Coq_inleft Coq_right 
                 else Coq_inright)".

Recursive Extraction Library AutoLMod.