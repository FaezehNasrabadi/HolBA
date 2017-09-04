open HolKernel Parse boolLib bossLib;
open wordsTheory bitstringTheory ASCIInumbersTheory;
open pred_setTheory;

val _ = new_theory "bir_auxiliary";

(* -------------------------------------------------------------------------- *)
(* List lemmata                                                               *)
(* -------------------------------------------------------------------------- *)

val LAST_FILTER_EL = store_thm ("LAST_FILTER_EL",
  ``!P l. (FILTER P l <> []) ==> (
          (?i. (i < LENGTH l) /\ (LAST (FILTER P l) = EL i l) /\ P (EL i l) /\
               (!j. i < j /\ j < LENGTH l ==> ~(P (EL j l)))))``,
GEN_TAC >> Induct >- (
  SIMP_TAC list_ss []
) >>
SIMP_TAC list_ss [] >>
CONV_TAC (RENAME_VARS_CONV ["e1"]) >>
REPEAT STRIP_TAC >>
Cases_on `FILTER P l = []` >| [
  Q.EXISTS_TAC `0` >>
  Cases_on `P e1` >> FULL_SIMP_TAC list_ss [] >>
  REPEAT STRIP_TAC >>
  `MEM (EL j (e1::l)) (FILTER P l)` suffices_by ASM_SIMP_TAC list_ss [] >>
  SIMP_TAC std_ss [listTheory.MEM_FILTER] >>
  ASM_SIMP_TAC list_ss [listTheory.MEM_EL] >>
  Q.EXISTS_TAC `PRE j` >>
  Cases_on `j` >> FULL_SIMP_TAC list_ss [],

  FULL_SIMP_TAC list_ss [] >>
  Q.EXISTS_TAC `SUC i` >>
  ASM_SIMP_TAC (list_ss++boolSimps.LIFT_COND_ss) [listTheory.LAST_DEF] >>
  REPEAT STRIP_TAC >>
  Cases_on `j` >> FULL_SIMP_TAC list_ss [] >>
  METIS_TAC[]
]);


val LENGTH_LASTN_LE = store_thm ("LENGTH_LASTN_LE",
  ``!n l. LENGTH (LASTN n l) <= LENGTH l``,

SIMP_TAC list_ss [rich_listTheory.LASTN_def,
  listTheory.LENGTH_TAKE_EQ]);


val dropWhile_MAP = store_thm ("dropWhile_MAP",
  ``!P f l. dropWhile P (MAP f l) =
            MAP f (dropWhile (P o f) l)``,

GEN_TAC >> GEN_TAC >>
Induct >> ASM_SIMP_TAC list_ss [] >>
GEN_TAC >> COND_CASES_TAC >> (
  SIMP_TAC list_ss []
))

val DROP_GENLIST = store_thm ("DROP_GENLIST",
  ``!n (f:num->'a) m.
      DROP n (GENLIST f m) =
      GENLIST (\n'. (f (n' + n))) (m - n)``,
Induct >- (
  SIMP_TAC (list_ss++boolSimps.ETA_ss) []
) >>
GEN_TAC >> Cases >- (
  SIMP_TAC list_ss []
) >>
ASM_SIMP_TAC list_ss [listTheory.GENLIST_CONS, arithmeticTheory.ADD_CLAUSES])


val INDEX_FIND_EQ_NONE = store_thm ("INDEX_FIND_EQ_NONE",
  ``!l i P. (INDEX_FIND i P l = NONE) <=> (~(EXISTS P l))``,
Induct >> SIMP_TAC list_ss [listTheory.INDEX_FIND_def] >>
REPEAT GEN_TAC >> COND_CASES_TAC >> ASM_SIMP_TAC list_ss []);


val INDEX_FIND_EQ_SOME = store_thm ("INDEX_FIND_EQ_SOME",
  ``!l i P j e. (INDEX_FIND i P l = SOME (j, e)) <=> (
       (i <= j) /\ (j - i < LENGTH l) /\
       (EL (j - i) l = e) /\ P e /\
       (!j'. (i <= j' /\ j' < j) ==> ~(P (EL (j' - i) l))))``,

Induct >> SIMP_TAC list_ss [listTheory.INDEX_FIND_def] >>
REPEAT GEN_TAC >> COND_CASES_TAC >| [
  SIMP_TAC list_ss [] >>
  EQ_TAC >| [
    SIMP_TAC list_ss [] >>
    PROVE_TAC[],

    STRIP_TAC >>
    Cases_on `i < j` >| [
      `~(P (EL (i - i) (h :: l)))` by METIS_TAC[arithmeticTheory.LESS_EQ_REFL] >>
      FULL_SIMP_TAC list_ss [],

      `i = j` by DECIDE_TAC >>
      FULL_SIMP_TAC list_ss []
    ]
  ],

  ONCE_ASM_REWRITE_TAC[] >>
  EQ_TAC >> STRIP_TAC >> ASM_SIMP_TAC list_ss [] >| [
     REPEAT STRIP_TAC >- (
       `j - i = SUC (j - SUC i)` by DECIDE_TAC >>
       ASM_SIMP_TAC list_ss []
     ) >>
     Cases_on `i = j'` >- (
       FULL_SIMP_TAC list_ss []
     ) >>
     Q.PAT_X_ASSUM `!j'. _ ==> ~(P _)` (MP_TAC o Q.SPEC `j'`) >>
     `j' - i = SUC (j' - SUC i)` by DECIDE_TAC >>
     FULL_SIMP_TAC list_ss [],


     Cases_on `i = j` >- (
       FULL_SIMP_TAC list_ss []
     ) >>
     `j - i = SUC (j - SUC i)` by DECIDE_TAC >>
     FULL_SIMP_TAC list_ss [] >>
     REPEAT STRIP_TAC >>
     Q.PAT_X_ASSUM `!j'. _ ==> ~(P _)` (MP_TAC o Q.SPEC `j'`) >>
     `j' - i = SUC (j' - SUC i)` by DECIDE_TAC >>
     FULL_SIMP_TAC list_ss []
  ]
]);


val INDEX_FIND_EQ_SOME_0 = store_thm ("INDEX_FIND_EQ_SOME_0",
  ``!l P j e. (INDEX_FIND 0 P l = SOME (j, e)) <=> (
       (j < LENGTH l) /\
       (EL j l = e) /\ P e /\
       (!j'. j' < j ==> ~(P (EL j' l))))``,

SIMP_TAC (std_ss++boolSimps.EQUIV_EXTRACT_ss) [INDEX_FIND_EQ_SOME] >>
Cases_on `LENGTH l` >> SIMP_TAC std_ss []);


val SEG_SUC_LENGTH = store_thm ("SEG_SUC_LENGTH",
``!l n m. (n + m < LENGTH l) ==>
          (SEG (SUC n) m l = (EL m l)::SEG n (SUC m) l)``,

SIMP_TAC arith_ss [rich_listTheory.SEG_TAKE_BUTFISTN] >>
REPEAT STRIP_TAC >>
ASM_SIMP_TAC list_ss [rich_listTheory.DROP_EL_CONS, arithmeticTheory.ADD1]);


(* -------------------------------------------------------------------------- *)
(* While lemmata                                                              *)
(* -------------------------------------------------------------------------- *)

val LEAST_SUC = store_thm ("LEAST_SUC",
``!P. ~(P 0) /\ (?i. P i) ==> ((LEAST i. P i) = SUC (LEAST i. P (SUC i)))``,

REPEAT STRIP_TAC >>
`?i'. i = SUC i'` by (
  Cases_on `i` >> FULL_SIMP_TAC arith_ss []
) >>
BasicProvers.VAR_EQ_TAC >>
DEEP_INTRO_TAC whileTheory.LEAST_ELIM >>
REPEAT STRIP_TAC >- METIS_TAC[] >>
DEEP_INTRO_TAC whileTheory.LEAST_ELIM >>
REPEAT STRIP_TAC >- METIS_TAC[] >>
rename1 `n1' = SUC n2` >>
`?n1. n1' = SUC n1` by (
  Cases_on `n1'` >> FULL_SIMP_TAC arith_ss []
) >>
BasicProvers.VAR_EQ_TAC >>

`~(SUC n2 < SUC n1)` by METIS_TAC[] >>
`~(n1 < n2)` by METIS_TAC[] >>
DECIDE_TAC);


(* -------------------------------------------------------------------------- *)
(* Optional Minimum                                                           *)
(* -------------------------------------------------------------------------- *)

val OPT_NUM_MIN_def = Define `
   (OPT_NUM_MIN NONE no2 = no2) /\
   (OPT_NUM_MIN no1 NONE = no1) /\
   (OPT_NUM_MIN (SOME n1) (SOME n2) = SOME (MIN n1 n2))`;


val OPT_NUM_MIN_REWRS = store_thm ("OPT_NUM_MIN_REWRS",
`` (!no. (OPT_NUM_MIN NONE no = no)) /\
   (!no. (OPT_NUM_MIN no NONE = no)) /\
   (!n1 n2. (OPT_NUM_MIN (SOME n1) (SOME n2) = SOME (MIN n1 n2)))``,

REPEAT CONJ_TAC >> REPEAT Cases >>
SIMP_TAC std_ss [OPT_NUM_MIN_def]);


val OPT_NUM_MIN_COMM = store_thm ("OPT_NUM_MIN_COMM",
``!no1 no2. (OPT_NUM_MIN no1 no2 = OPT_NUM_MIN no2 no1)``,

Cases >> Cases >> SIMP_TAC std_ss [OPT_NUM_MIN_REWRS] >>
METIS_TAC[arithmeticTheory.MIN_COMM]);


val OPT_NUM_MIN_ASSOC = store_thm ("OPT_NUM_MIN_ASSOC",
``!no1 no2 no3. (OPT_NUM_MIN no1 (OPT_NUM_MIN no2 no3)) = OPT_NUM_MIN (OPT_NUM_MIN no1 no2) no3``,

Cases >> Cases >> Cases >> SIMP_TAC std_ss [OPT_NUM_MIN_REWRS] >>
METIS_TAC[arithmeticTheory.MIN_ASSOC]);


val OPT_NUM_MIN_SOME0 = store_thm ("OPT_NUM_MIN_SOME0",
``(!no. (OPT_NUM_MIN no (SOME 0)) = SOME 0) /\
  (!no. (OPT_NUM_MIN (SOME 0) no) = SOME 0)``,

REPEAT CONJ_TAC >> (
  Cases >> SIMP_TAC std_ss [OPT_NUM_MIN_REWRS]
));


val OPT_NUM_MIN_CASES = store_thm ("OPT_NUM_MIN_CASES",
``!no1 no2. (OPT_NUM_MIN no1 no2 = no1) \/
            (OPT_NUM_MIN no1 no2 = no2)``,

REPEAT Cases >>
SIMP_TAC std_ss [OPT_NUM_MIN_REWRS, arithmeticTheory.MIN_DEF] >>
METIS_TAC[]);



val OPT_NUM_PRE_def = Define `OPT_NUM_PRE = OPTION_MAP PRE`;
val OPT_NUM_SUC_def = Define `OPT_NUM_SUC = OPTION_MAP SUC`;

val OPT_NUM_PRE_SUC = store_thm ("OPT_NUM_PRE_SUC",
  ``!no. OPT_NUM_PRE (OPT_NUM_SUC no) = no``,
Cases >> SIMP_TAC std_ss [OPT_NUM_PRE_def, OPT_NUM_SUC_def]);


val OPT_NUM_MIN_SOME_SUC_aux = prove (
``(!no n. (OPT_NUM_MIN no (SOME (SUC n))) = if (no = SOME 0) then SOME 0 else
     SOME (SUC (THE (OPT_NUM_MIN (OPT_NUM_PRE no) (SOME n)))))``,

Cases >> (
  SIMP_TAC std_ss [OPT_NUM_MIN_REWRS, arithmeticTheory.MIN_DEF, OPT_NUM_PRE_def]
) >>
GEN_TAC >>
rename1 `x < SUC n` >>
Cases_on `x` >> SIMP_TAC arith_ss []);


val OPT_NUM_MIN_SOME_SUC = save_thm ("OPT_NUM_MIN_SOME_SUC",
  CONJ OPT_NUM_MIN_SOME_SUC_aux
       (ONCE_REWRITE_RULE [OPT_NUM_MIN_COMM] OPT_NUM_MIN_SOME_SUC_aux));


val OPT_NUM_MIN_OPT_NUM_SUC_aux = prove (
``(!no1 no2. (OPT_NUM_MIN no1 (OPT_NUM_SUC no2)) = if (no1 = SOME 0) then SOME 0 else
     OPT_NUM_SUC (OPT_NUM_MIN (OPT_NUM_PRE no1) no2))``,

Cases_on `no2` >- (
  Cases_on `no1` >> (
    SIMP_TAC std_ss [OPT_NUM_SUC_def, OPT_NUM_PRE_def, OPT_NUM_MIN_REWRS]
  ) >>
  rename1 `SOME n  = _` >> Cases_on `n` >> SIMP_TAC arith_ss []
) >>
SIMP_TAC std_ss [OPT_NUM_SUC_def, OPT_NUM_MIN_SOME_SUC] >>
Cases_on `no1` >> (
   SIMP_TAC std_ss [OPT_NUM_MIN_REWRS, OPT_NUM_PRE_def, OPT_NUM_SUC_def]
));

val OPT_NUM_MIN_OPT_NUM_SUC = save_thm ("OPT_NUM_MIN_OPT_NUM_SUC",
  CONJ OPT_NUM_MIN_OPT_NUM_SUC_aux
       (ONCE_REWRITE_RULE [OPT_NUM_MIN_COMM] OPT_NUM_MIN_OPT_NUM_SUC_aux));

val OPT_CONS_def = Define `OPT_CONS eo l = option_CASE eo l (\e. CONS e l)`

val OPT_CONS_REWRS = store_thm ("OPT_CONS_REWRS",
  ``(!l. OPT_CONS NONE l = l) /\
    (!e l. OPT_CONS (SOME e) l = e::l)``,
SIMP_TAC std_ss [OPT_CONS_def]);


val OPT_CONS_APPEND = store_thm ("OPT_CONS_APPEND",
  ``!eo l1 l2. (OPT_CONS eo l1) ++ l2 =
      OPT_CONS eo (l1 ++ l2)``,
Cases >> SIMP_TAC list_ss [OPT_CONS_REWRS]);


val OPT_CONS_REVERSE = store_thm ("OPT_CONS_REVERSE",
  ``!eo l. REVERSE (OPT_CONS eo l) = REVERSE l ++ OPT_CONS eo []``,
Cases >> SIMP_TAC list_ss [OPT_CONS_REWRS]);



(* -------------------------------------------------------------------------- *)
(* lazy lists                                                                 *)
(* -------------------------------------------------------------------------- *)

val LGENLIST_UNFOLD_NONE = store_thm ("LGENLIST_UNFOLD_NONE",
  ``!f. LGENLIST f NONE = (f 0) ::: (LGENLIST (f o SUC) NONE)``,

SIMP_TAC arith_ss [llistTheory.LGENLIST_EQ_CONS,
  combinTheory.o_DEF, GSYM arithmeticTheory.ADD1]);


val LGENLIST_UNFOLD_NEQ_SOME0 = store_thm ("LGENLIST_UNFOLD_NEQ_SOME0",
  ``!no f. (no <> SOME 0) ==> (LGENLIST f no = (f 0) ::: (LGENLIST (f o SUC) (OPT_NUM_PRE no)))``,

Cases >- (
  SIMP_TAC std_ss [OPT_NUM_PRE_def] >>
  METIS_TAC[LGENLIST_UNFOLD_NONE]
) >>
rename1 `SOME n <> SOME 0` >>
Cases_on `n` >- (
  SIMP_TAC std_ss []
) >>
rename1 `SOME (SUC n') <> SOME 0` >>
SIMP_TAC std_ss [llistTheory.LGENLIST_SOME, OPT_NUM_PRE_def]);


val OPT_LCONS_def = Define `OPT_LCONS eo l = option_CASE eo l (\e. LCONS e l)`

val OPT_LCONS_REWRS = store_thm ("OPT_LCONS_REWRS",
  ``(!ll. OPT_LCONS NONE ll = ll) /\
    (!e ll. OPT_LCONS (SOME e) ll = e:::ll)``,
SIMP_TAC std_ss [OPT_LCONS_def]);


val OPT_CONS_fromList = store_thm ("OPT_CONS_fromList",
  ``!eo l. fromList (OPT_CONS eo l) = OPT_LCONS eo (fromList l)``,

Cases >> SIMP_TAC std_ss [OPT_CONS_REWRS, OPT_LCONS_REWRS, llistTheory.fromList_def]);


val LMAP_EQ_LNIL = store_thm ("LMAP_EQ_LNIL",
``!f ll. (LMAP f ll = LNIL) <=> (ll = LNIL)``,

Cases_on `ll` >> (
  SIMP_TAC std_ss [llistTheory.LMAP, llistTheory.LCONS_NOT_NIL]
));


(* -------------------------------------------------------------------------- *)
(* Word lemmata                                                               *)
(* -------------------------------------------------------------------------- *)


val w2n_MOD_2EXP_ID = store_thm ("w2n_MOD_2EXP_ID",
  ``!(w:'a word). (MOD_2EXP (dimindex (:'a)) (w2n w)) = w2n w``,
SIMP_TAC std_ss [GSYM wordsTheory.MOD_2EXP_DIMINDEX, wordsTheory.w2n_lt]);

val word_extract_bits_w2w = store_thm ("word_extract_bits_w2w",
  ``!h l a. ((h >< l) (a:'a word)) = w2w ((h -- l) a)``,
SIMP_TAC std_ss [wordsTheory.word_extract_w2w_mask, wordsTheory.word_bits_mask])

val sw2sw_w2w_downcast = store_thm ("sw2sw_w2w_downcast", ``!w.
  (dimindex (:'b) <= dimindex (:'a)) ==> ((sw2sw (w : 'a word) : 'b word) = w2w w)``,

REPEAT STRIP_TAC >>
`(2**dimindex (:'b) <= 2**dimindex (:'a))` by METIS_TAC[bitTheory.TWOEXP_MONO2] >>
`(2**dimindex (:'b) - 2**dimindex (:'a)) = 0` by DECIDE_TAC >>
ASM_SIMP_TAC (arith_ss++wordsLib.WORD_ss) [sw2sw_def,
  bitTheory.SIGN_EXTEND_def, LET_DEF, w2w_def,
  wordsTheory.w2n_lt, GSYM wordsTheory.dimword_def
]);


val fixwidth_fixwidth_le = store_thm ("fixwidth_fixwidth_le",
  ``!v n m. n <= m ==> (fixwidth n (fixwidth m v) = fixwidth n v)``,

REPEAT STRIP_TAC >>
`LENGTH (fixwidth m v) = m` by SIMP_TAC std_ss [length_fixwidth] >>
FULL_SIMP_TAC list_ss [LET_DEF, fixwidth_def] >>
REPEAT COND_CASES_TAC >| [
  FULL_SIMP_TAC list_ss [zero_extend_def, listTheory.PAD_LEFT,
    rich_listTheory.DROP_APPEND1, DROP_GENLIST, combinTheory.K_DEF],

  FULL_SIMP_TAC list_ss [zero_extend_def, listTheory.PAD_LEFT,
    rich_listTheory.DROP_APPEND2],

  FULL_SIMP_TAC arith_ss [],

  ASM_SIMP_TAC arith_ss [rich_listTheory.DROP_DROP_T]
]);


val w2v_word_join = store_thm ("w2v_word_join",
``FINITE univ(:'a) /\ FINITE univ(:'b) ==>
  !w1:'a word w2:'b word. w2v (word_join w1 w2) = (w2v w1 ++ w2v w2)``,

REPEAT STRIP_TAC >>
bitstringLib.Cases_on_v2w `w1` >>
bitstringLib.Cases_on_v2w `w2` >>
ASM_SIMP_TAC (list_ss++wordsLib.SIZES_ss) [w2v_v2w, fixwidth_id_imp,
  word_join_v2w, fcpTheory.index_sum]);


val w2v_word_concat = store_thm ("w2v_word_concat",
``FINITE univ(:'a) /\ FINITE univ(:'b) /\ (dimindex (:'c) = dimindex (:'a) + dimindex (:'b)) ==>
  !w1:'a word w2:'b word. w2v ((w1 @@ w2):'c word) = (w2v w1 ++ w2v w2)``,

REPEAT STRIP_TAC >>
bitstringLib.Cases_on_v2w `w1` >>
bitstringLib.Cases_on_v2w `w2` >>
ASM_SIMP_TAC (list_ss++wordsLib.SIZES_ss) [w2v_v2w, fixwidth_id_imp, word_concat_def,
  word_join_v2w, fcpTheory.index_sum, w2w_def, w2n_v2w, bitTheory.MOD_2EXP_def] >>
`v2n (v ++ v') < 2 ** (LENGTH v + LENGTH v')` by (
  METIS_TAC[bitstringTheory.v2n_lt, listTheory.LENGTH_APPEND]
) >>
ASM_SIMP_TAC list_ss [n2w_v2n, w2v_v2w, fixwidth_id_imp]);


val w2v_word_concat_SYM_REWRS = save_thm ("w2v_word_concat_SYM_REWRS",
let
  val words_sizes = [1,8,16,32,64]
  val max_ws = last words_sizes

  val thm_idx = LIST_CONJ (for 1 (max_ws+max_ws) (fn i => fcpLib.DIMINDEX (Arbnum.fromInt i)))
  val thm_fin = LIST_CONJ (for 1 max_ws (fn i => fcpLib.FINITE (Arbnum.fromInt i)))

  val rewr_tac = REWRITE_TAC [thm_fin, thm_idx];

  val thm0 = GSYM w2v_word_concat
  fun inst_w2v_word_concat n m = let
    val n_ty = fcpLib.index_type (Arbnum.fromInt n);
    val m_ty = fcpLib.index_type (Arbnum.fromInt m);
    val nm_ty = fcpLib.index_type (Arbnum.fromInt (n+m));

    val thm1a = INST_TYPE [``:'a`` |-> n_ty, ``:'b`` |-> m_ty, ``:'c`` |-> nm_ty] thm0
    val (pre, _) = dest_imp (concl(thm1a))
    val pre_thm = prove (pre, rewr_tac >> DECIDE_TAC)
    val thm1 = MP thm1a pre_thm
  in thm1 end

  fun words_sizes_combs_n s c = (if (c+s) <= max_ws then (s, c)::(c,s)::words_sizes_combs_n s (c+s) else [])
  val words_sizes_combs = flatten (map (fn n => words_sizes_combs_n n n) words_sizes)

  val thm1 = LIST_CONJ (map (fn (n, m) => inst_w2v_word_concat m n) words_sizes_combs)
in
  thm1
end)


val word1_dichotomy = store_thm ("word1_dichotomy",
  ``!v:word1. (v = 1w) \/ (v = 0w)``,
Cases >>
FULL_SIMP_TAC (std_ss++wordsLib.WORD_ss) [wordsTheory.n2w_11] >>
DECIDE_TAC);

val word1_distinct = store_thm ("word1_distinct",
  ``(1w:word1) <> 0w``,
SIMP_TAC (std_ss++wordsLib.WORD_ss) []);


(* -------------------------------------------------------------------------- *)
(* Fresh variable names                                                       *)
(* -------------------------------------------------------------------------- *)

val FRESH_INDEXED_STRING_MK_def = Define `FRESH_INDEXED_STRING_MK pre n =
  (pre ++ (num_to_dec_string n))`;

val FRESH_INDEXED_STRING_MK_11 = store_thm ("FRESH_INDEXED_STRING_MK_11",
``!pre n1 n2. (FRESH_INDEXED_STRING_MK pre n1 = FRESH_INDEXED_STRING_MK pre n2) <=> (n1 = n2)``,
SIMP_TAC list_ss [FRESH_INDEXED_STRING_MK_def, toString_11]);

val FRESH_INDEXED_STRING_AUX_def = Define `
  FRESH_INDEXED_STRING_AUX pre n s = (LEAST x. (n <= x) /\ ~((FRESH_INDEXED_STRING_MK pre x) IN s))`;

val FRESH_INDEXED_STRING_def = Define `
  FRESH_INDEXED_STRING pre n s = (FRESH_INDEXED_STRING_MK pre (FRESH_INDEXED_STRING_AUX pre n s))`;

val FRESH_INDEXED_STRINGS_def = Define `
  (FRESH_INDEXED_STRINGS pre n s 0 = []) /\
  (FRESH_INDEXED_STRINGS pre n s (SUC m) =
   let ns = (FRESH_INDEXED_STRING_AUX pre n s) in
   let ss = FRESH_INDEXED_STRING_MK pre ns in
   (ss::FRESH_INDEXED_STRINGS pre (SUC ns) s m))`;


val FRESH_INDEXED_STRING_AUX_PROPS = prove (``!s pre n i.
  FINITE s ==>
  let i = FRESH_INDEXED_STRING_AUX pre n s in
  (n <= i) /\ ~(FRESH_INDEXED_STRING_MK pre i IN s) /\
  (!i'. (n <= i' /\ i' < i) ==> ((FRESH_INDEXED_STRING_MK pre i') IN s))``,

SIMP_TAC std_ss [LET_THM, FRESH_INDEXED_STRING_AUX_def] >>
REPEAT GEN_TAC >> STRIP_TAC >>
numLib.LEAST_ELIM_TAC >>
REPEAT STRIP_TAC >| [
  ALL_TAC,
  ASM_REWRITE_TAC[],
  METIS_TAC[]
] >>

Q.ABBREV_TAC `S0 = count n` >>
Q.ABBREV_TAC `S1 = (UNIV:num set) DIFF S0` >>
Q.ABBREV_TAC `S2 = (IMAGE (FRESH_INDEXED_STRING_MK pre) S1)` >>


`INFINITE S1` by METIS_TAC[FINITE_DIFF_down, FINITE_COUNT, INFINITE_NUM_UNIV] >>
`INFINITE S2` by METIS_TAC[FRESH_INDEXED_STRING_MK_11, IMAGE_11_INFINITE] >>

`?ns. ns IN S2 /\ ~(ns IN s)` by METIS_TAC[pred_setTheory.IN_INFINITE_NOT_FINITE] >>
UNABBREV_ALL_TAC >>
FULL_SIMP_TAC arith_ss [IN_IMAGE, IN_DIFF, IN_COUNT, IN_UNIV, arithmeticTheory.NOT_LESS] >>
METIS_TAC[]);



val FRESH_INDEXED_STRING_NOT_IN = store_thm ("FRESH_INDEXED_STRING_NOT_IN",
  ``!s pre n. FINITE s ==> ~(FRESH_INDEXED_STRING pre n s IN s)``,
SIMP_TAC std_ss [FRESH_INDEXED_STRING_def] >>
METIS_TAC[FRESH_INDEXED_STRING_AUX_PROPS]);


val FRESH_INDEXED_STRINGS_PROPS_INDICES = store_thm ("FRESH_INDEXED_STRINGS_PROPS_INDICES",
  ``!s pre l n. FINITE s ==> (
       ?nl. (FRESH_INDEXED_STRINGS pre n s l = MAP (FRESH_INDEXED_STRING_MK pre) nl) /\
            (LENGTH nl = l) /\
            (ALL_DISTINCT nl) /\
            (EVERY ($<= n) nl) /\
            (EVERY (\n. ~((FRESH_INDEXED_STRING_MK pre n) IN s)) nl))``,

GEN_TAC >> GEN_TAC >>
Induct >> (
  SIMP_TAC list_ss [FRESH_INDEXED_STRINGS_def, LET_THM]
) >>
REPEAT STRIP_TAC >>
FULL_SIMP_TAC std_ss [] >>
Q.ABBREV_TAC `n' = FRESH_INDEXED_STRING_AUX pre n s` >>
Q.PAT_X_ASSUM `!n. _` (STRIP_ASSUME_TAC o Q.SPEC `SUC n'`) >>
Q.EXISTS_TAC `n'::nl` >>
FULL_SIMP_TAC list_ss [listTheory.EVERY_MEM] >>
`n <= n' /\ ~(FRESH_INDEXED_STRING_MK pre n' IN s)` by METIS_TAC[FRESH_INDEXED_STRING_AUX_PROPS] >>
ASM_REWRITE_TAC[] >>
REPEAT STRIP_TAC >| [
  `SUC n' <= n'` by PROVE_TAC[] >>
  DECIDE_TAC,

  `SUC n' <= e` by PROVE_TAC[] >>
  DECIDE_TAC
]);


val FRESH_INDEXED_STRINGS_PROPS = store_thm ("FRESH_INDEXED_STRING_PROPS",
  ``!s pre l n. FINITE s ==> (
      (LENGTH (FRESH_INDEXED_STRINGS pre n s l) = l) /\
      ALL_DISTINCT (FRESH_INDEXED_STRINGS pre n s l) /\
      (EVERY (\n. ~(n IN s)) (FRESH_INDEXED_STRINGS pre n s l)))``,


REPEAT GEN_TAC >>
ASSUME_TAC (Q.SPECL [`s`, `pre`, `l`, `n`] FRESH_INDEXED_STRINGS_PROPS_INDICES) >>
STRIP_TAC >>
FULL_SIMP_TAC list_ss [listTheory.EVERY_MAP] >>
MATCH_MP_TAC listTheory.ALL_DISTINCT_MAP_INJ >>
ASM_SIMP_TAC std_ss [FRESH_INDEXED_STRING_MK_11]);


val _ = export_theory();