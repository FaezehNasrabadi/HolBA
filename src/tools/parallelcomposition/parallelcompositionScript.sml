open HolKernel Parse boolLib bossLib;
open bagTheory;

val _ = new_theory "parallelcomposition";

(* transition relation *)
val _ = Parse.type_abbrev("trel", ``:(('symb set) # ('pred set) # 'state)  -> 'event -> (('symb set) # ('pred set) # 'state) -> bool``);    

(* deduction relation *)    
val _ = Parse.type_abbrev("tded", ``:('pred set) -> 'pred -> bool``);

(* transition system *)    
val _ = Parse.type_abbrev("transitionsystem", ``:(( 'symb, 'pred, 'state, 'event ) trel # ('pred) tded)``);


val _ = Parse.type_abbrev("ComOpr", 
  ``:('symb, 'pred1, 'state1, 'event1 + 'eventS) transitionsystem ->
  ('symb, 'pred2, 'state2, 'event2 + 'eventS) transitionsystem -> 
  ('symb, 'pred1 + 'pred2, 'state1 # 'state2, (('event1+'eventS) + ('event2 +'eventS))) transitionsystem``);




val _ = export_theory();
