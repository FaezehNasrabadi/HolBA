open HolKernel Parse boolLib bossLib;
open sumTheory;
open pred_setTheory;

val _ = new_theory "parallelcomposition";

    
(* transition relation *)
val _ = Parse.type_abbrev("trel", ``:'state -> 'event -> 'state -> bool``);    

    

val _ = Parse.type_abbrev("ComOpr", 
  ``:('state1,'event1 + 'eventS) trel ->
  ('state2, 'event2 + 'eventS) trel -> 
  ('state1 # 'state2, (('event1+'eventS) + ('event2 +'eventS))) trel``);


(* multi transitions relation *)
val _ = Parse.type_abbrev("mtrel", ``:'state -> ('event list) -> 'state -> bool``);


(* compose multi transition relation *)
val _ = Parse.type_abbrev("cmtrel", ``:('state1, 'event1 + 'eventS) mtrel ->
  ('state2, 'event2 + 'eventS) mtrel -> 
  ('state1 # 'state2, (('event1+'eventS) + ('event2 +'eventS))) mtrel``);
     

val composeMuRe_def =
Define  `
((composeMuRe (Re1:(('event1 + 'eventS), 'state1) mtrel) (Re2:(('event2 + 'eventS), 'state2) mtrel) (S1,S2) [] (S1',S2')) =
         (((S1,S2) = (S1',S2'))∧(Re1 S1 [] S1)∧(Re2 S2 [] S2)))  ∧
((composeMuRe (Re1:(('event1 + 'eventS), 'state1) mtrel) (Re2:(('event2 + 'eventS), 'state2) mtrel) (S1,S2) ((INL (INL (E:'event1)))::ev) (S1'',S2')) =
 (∃S1'. (Re1 S1' [INL E] S1'')∧(Re2 S2' [] S2') ∧(composeMuRe Re1 Re2 (S1,S2) ev (S1',S2')))) ∧
((composeMuRe (Re1:(('event1 + 'eventS), 'state1) mtrel) (Re2:(('event2 + 'eventS), 'state2) mtrel) (S1,S2) ((INR (INL (E:'event2)))::ev) (S1',S2'')) =
 (∃S2'. (Re2 S2' [INL E] S2'')∧(Re1 S1' [] S1') ∧(composeMuRe Re1 Re2 (S1,S2) ev (S1',S2')))) ∧
((composeMuRe (Re1:(('event1 + 'eventS), 'state1) mtrel) (Re2:(('event2 + 'eventS), 'state2) mtrel) (S1,S2) ((INR (INR (E:'eventS)))::ev) (S1'',S2'')) =
 (∃S1' S2'. (Re1 S1' [INR E] S1'')∧(Re2 S2' [INR E] S2'') ∧ (composeMuRe Re1 Re2 (S1,S2) ev (S1',S2')))) ∧
((composeMuRe (Re1:(('event1 + 'eventS), 'state1) mtrel) (Re2:(('event2 + 'eventS), 'state2) mtrel) (S1,S2) ((INL (INR (E:'eventS)))::ev) (S1'',S2'')) =
 (∃S1' S2'. (Re1 S1' [INR E] S1'')∧(Re2 S2' [INR E] S2'')∧ (composeMuRe Re1 Re2 (S1,S2) ev (S1',S2'))))
`;


val _ = set_mapped_fixity { fixity = Infixl 95,
                            term_name = "apply_composeMuRe",
                            tok = "||" };

val _ = overload_on ("apply_composeMuRe", ``composeMuRe``);

val _ = export_theory();

