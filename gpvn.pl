/* PROGRAM:  gpvn.pl
 * CREATED:  9.18.87
 * UPDATED:  9.3.90
 * AUTHORS:  CVBII & PBMVIII
 * PURPOSE:  evaluates formula in a four valued semantics
 * NOTES..:  to be run/compiled under Arity Prolog :
 * UPDATED:  Sun Oct 10 12:48:14 1999 EDT
 * NOTES..:  modified to run under GNU Prolog 1.0.0 :
 *           - first removed everything not directly related to
 *             interpretation, valuation or translation,
 *           - translated 'not' as '\+' , (3 occurances)
 *           - translated '$' to ''', (6 occurances)
 *           - removed definitions for append and member
 *           - translated ':- extrn ' to 'dynamic('
 * UPDATED:  Mon Jan 2 20:49:08 2006 UTC
 * NOTES..:  modified to run under SWI-Prolog Version 5.6.0
 *           - changed dynamic predicate declaration syntax,
 *           - rename index to avoid name collision and
 *           - constant definitions for sentance variables.
 * UPDATED:  Fri 10 Sep 2021 12:44:30 PM EDT
 * NOTES..:  modified to run under gprolog 1.5.0 
 *           - changes assert/1 to asserta/1
 */
 
public(
     iv/3,
     val/4,
     gnu/0,
     swap_table/0,
     chg_tbl/1,
     do_n_value/2,
     empty_table/0,
     quick_help/0,
     help/0,
     explain/0,
     check_formula/1,
     check_polarity/2,
     counter_example/2,
     display_var_data/0,
     disp_var_data/1,
     display_variable_set/0,
     get_var_set/2,
     disp_var_set/1,
     beep/2,
     translate/2,
     trans/2,
     append/3,
     member/2 ).

dynamic :- 
  define/4,
  define/3,
  define/2, 
  define/1, 
  define_matrix/1, 
  transindex/1, 
  sentence_var/1,
  var_data/1,
  var_set/1, 
  polarity/1, 
  ax/1.




:- op(952,yfx,@).
:- op(952,yfx,&).
:- op(952,yfx,v).
:- op(952,xfx,>).
:- op(950,fx,^).


/*---------------  general interpretation rule ------------------------*/

/*
    The interpretation function 'iv' has three terms.  The first term is
    the 'Formula' to be interpreted.  The second term is the truth value
    interpretation of the 'Formula'.  The third term is a list with two
    lists as elements.  The first element is a list of the assignments of
    truth values to variables prior to 'iv', and the second element is a
    list of the variable assignments after 'iv' succeeds.  'iv' succeeds
    if the interpretation of the component parts of the 'Formula' result
    in a consistent assignment of truth values to the variables.

    A clause is needed for each type of formula to be interpreted:
          -    2-ary  &, v, >,
          -    1-ary  ^,
          -    0-ary  atomic formula.
*/

/*  First the rule for interpreting two place complex formula. */

iv(Formula,Result,[Pre_set_variables,Variables_set_here]):-
    Formula =.. [Operator,Operand1,Operand2],
    define(Operator,Result,Assignment1,Assignment2),
    iv(Operand1,Assignment1,[Pre_set_variables,Some_variables]),
    append(Pre_set_variables,Some_variables,New_context),
    iv(Operand2,Assignment2,[New_context,More_variables]),
    append(Some_variables,More_variables,Variables_set_here).

/*  Next the rule for interpreting one place complex formula. */

iv(Formula,Result,[Pre_set_variables,Variables_set_here]):-
    Formula =.. [Operator,Operand],
    define(Operator,Result,Assignment),
    iv(Operand,Assignment,[Pre_set_variables,Variables_set_here]).

/*  Now the general rule for interpreting atomic formulas. */

iv(atm(Type,Index),Value,[Pre_set_variables,Variables_set_here]) :-
    val(Type,Index,Value,[Pre_set_variables,Variables_set_here]).


/*
    ----------------------------------------------------
    if the variable has already been set to a value,
    the clause succeeds and returns the null set as the
    variables_set_here.
    ----------------------------------------------------
*/

val(var,Index,Value,[Pre_set_var,[]]):-
    member([Index,Anything],Pre_set_var),
    Value = Anything.

/*
    ------------------------------------------------
    if the variable has already been set to a value,
    the compare clause fails, the third val clause
    should not be used.
    ------------------------------------------------
*/

val(var,Index,Value,[Pre_set_var,[]]):-
    member([Index,Anything],Pre_set_var),
    \+ Value = Anything,
    !,
    fail.

/*
    ---------------------------------------------------
    otherwise the variable is set to a constant value,
    the clause succeeds and returns the index and value
    as the variables_set_here.
    ---------------------------------------------------
*/

val(var,Index,Value,[Pre_set_var,[[Index,Value]]]):-
    val(con,Value,Value,It_is_the_same).

    /*================*/
    /* screen display */
    /*================
    ( \+ recorded('automate', silent, REF1) ) ->
      (
       Row is Index + 2,
       tmove(Row,16),
       write(Value)
      )
    ).
    */

val(con,Value,Value,[Pre_set_var,[]]) :- polarity(Value).

/*=============================================================
  --------- algebra to polish notation translation ------------
  =============================================================*/

inc(Last_index_used,Index) :- 
    Index is Last_index_used + 1.

translate(Formula,NewFormula) :-
    trans(Formula,NewFormula),
    pvn_emit_report([trans,Formula,NewFormula]).

trans(X,atm(var,Index)) :-
    call(sentence_var(X)),
    call(var_data(A)),
    \+ member([X,Y],A),
    call(transindex(Last_index_used)),
    inc(Last_index_used,Index),
    append([[X,Index]],A,Z),
    retract(transindex(G)),
    retract(var_data(H)),
    assertz(transindex(Index)),
    assertz(var_data(Z)).

trans(X,atm(var,Index)) :-
    call(sentence_var(X)),
    call(var_data(A)),
    member([X,Index],A).

trans(X,atm(con,X)) :-
    polarity(X).

trans(Old_formula,New_formula):-
    Old_formula =.. [Operator,Formula_1],
    define(Operator,Name),
    trans(Formula_1,T_formula_1),
    New_formula =.. [Name,T_formula_1].

trans(Old_formula,New_formula):-
    Old_formula =.. [Operator,Formula_1,Formula_2],
    define(Operator,Name),
    New_formula =.. [Name,T_formula_1,T_formula_2],
    trans(Formula_1,T_formula_1),
    trans(Formula_2,T_formula_2).


/** utility predicate to show current operator defines.
 */
show_def :-
    define_matrix(Line),
    write(Line), nl,
    fail.

show_def.

gnu :-
    write('gpvn ver. 2.3 :'),
    write('=:> '),
    read(Formula),
    translate(Formula,New),
    write('About to check formula'),nl,
    check_formula(New),
    reset,
    reset_var_set.


/* ---------------------------- */

reset :-
    retract(transindex(J)),
    assertz(transindex(0)),
    retract(var_data(O)),
    assertz(var_data([[z,index]])).

reset.

reset_var_set :-
    retract(var_set(_,_)),
    fail.

reset_var_set :-
    assertz(var_set([[],[]])).

/* ---------------------------- */

save_var_set(_,_) :-
    retract(var_set(_,_)),
    fail.

save_var_set(List_of_assignments,Result) :-
    assertz(var_set(Result,List_of_assignments)).

/************************************************************/
/*     check formula for having only one interpretation     */
/* ******************************************************** */
/* 'check_formula/1' takes as a value the formula that has  */
/* been translated into Polish notation. Using 'check_polarity/2' */
/* and 'counter_example/2' it determines whether the formula */
/* expresses a tautology, contradiction, or for that matter  */
/* neccessarily any polarity for the chosen logic.           */

check_formula(Formula) :-
    polarity(Polarity),
    check_polarity(Formula,Polarity).

check_formula(_) :-  
   /* write('Formula is contingent:'),nl, */ 
   pvn_emit_report([contingent]).


/* 'check_polarity/2' get passed the formula in polish notation */
/* and a polarity from 'check_formula/1'.  Using backtrack-fail */
/* to drive the choice of every possible polarity for that logic,*/
/* it passes the current formula and polarity to test it against */
/* to counter_example/2. 					*/

check_polarity(Formula,Fixed_polarity) :-
    polarity(Polarity),
    Polarity \= Fixed_polarity,
    write('about to check counter example'),nl,
    counter_example(Formula,Polarity),
    !,fail.
	
    
check_polarity(_,Polarity) :- 
	pvn_emit_report([check,Polarity]).


/** 'counter_example/2' succeeds when the clause 
 * 'not(iv(Formula,Polarity,Var_Settings))' fails. 
 *
 * It succeeds otherwise.  That is, when iv/3 is not 
 * able to find a consistent setting of variables to
 * polarities  that gives the Formula the value 
 * Other_polarity, then the first counter_example/2 
 * clause cuts, and fails back up to check_polarity/2 
 * which grabs another Polarity to check and sends the
 * Formula back to be tested with the new Polarity.
 *
 * If the iv/3 statement succeeds and the'not' fails that means
 * a set of polarities were found that succeeded in making the 
 * Formula = Polarity. This set of polarities is the counter example 
 * to the Formula being necessarily Polarity. 
 */

counter_example(Formula,Other_polarity) :-
     \+ ((iv(Formula,Other_polarity,[[],V1]),
          save_var_set(V1,Other_polarity))),
     !,fail.

counter_example(_,Other_polarity) :-
     pvn_emit_report([valset,Other_polarity]).


/* ---------------------------------------------------------------------
*/

go :- 
   do_n_value('pv4.df4',b),
   asserta(transindex(0)),
   asserta(var_data([[z,index]])).

do_n_value(Logic,Xtra) :-
    empty_table,
    write('Loading - '),
    write(Logic),
    consult(Logic),
    asserta(define(Logic)).
   


empty_table :-
    retract(define(Operator,Result,Operand_1,Operand_2)),
    fail.

empty_table :-
    retract(define(Operator,Result,Operand)),
    fail.

empty_table :-
     retract(define_matrix(_)),
     fail.

empty_table :-
     retract(define(_,_)),
     fail.

empty_table :-
     retract(polarity(_)),
     fail.

empty_table :-

    /*================*/
    /* screen display */
    /*================*/
    tmove(2,0),
    write('Finished retracting - '),
    retract(define(N)),
    write(N),nl.
    /*================*/



empty_table.


/*================*/
/* screen display */
/*================*/
tmove( _, _ ).


pvn_emit_report([trans,Formula,NewFormula]) :- 
   write('Translating formula : '),
   write(Formula),
   nl,
   write('Into : '),
   write(NewFormula),
   nl,nl,nl,
   !.  


pvn_emit_report([check,Polarity]) :-
   write('Polarity of Formula is always : '),
   write(Polarity),
   nl,!.

pvn_emit_report([contingent]) :- 
   write('Formula is Contingent. '),!,nl.

pvn_emit_report([valset,Other_polarity])  :- 
   get_var_set(List_of_assignments,Result),
   write('Polarity Formula can be : '),
   write(Other_polarity),nl,
   write('List of Assignments : '),
   write(List_of_assignments),nl,
   write('Result :'),
   write(Result),nl,!.

pvn_emit_report(_) :- !.



pvn_emit_list([]).
pvn_emit_list([Head|Tail]) :-
   write(Head),
   pvn_emit_list(Tail).

/* ---------------------------- */


/*=============================================================
  --------- variables for polish notation translation ---------
  =============================================================*/




sentence_var(a).
sentence_var(b).
sentence_var(c).
sentence_var(d).
sentence_var(e).


get_var_set(List_of_assignments,Result) :-
    call(var_set(Result,List_of_assignments)).


/* 
 * $Log: gpvn.pl,v $
 * Revision 1.7  2006/01/09 02:46:33  oommoo
 * another missive from pbm
 *
 * Revision 1.6  2006/01/03 05:31:42  oommoo
 * UPDATED comments
 *
 *
 */
