%{
#include <stdio.h>
extern int yylineno;
%}
%token ASSUME CASES CASE CONSIDER END LET NOW PROOF QED SET SUPPOSE TAKE THUS
%token EXEC
%token BE BEING BY FROM SUCH THAT
%token OTHER
/*     ',' ';' '[' ']' '(' ')'  */
%%
steplist
	: 
	| steplist step
	;
/*
xstep	: have_thus term labels by_just ';'
	| have_thus term labels
	  PROOF
	| NOW labels
	| LET identlist BE term ';'
	| ASSUME term labels ';'
	| TAKE term ';'
	| CONSIDER identlist opttype SUCH THAT term labels by_just ';'
	| CONSIDER identlist opttype SUCH THAT term labels
	  PROOF
	| SET term labels ';'
	| CASES by_just ';'
	| CASE ';'
	| SUPPOSE term labels ';'
	| QED by_just ';'
	| END ';'
	| EXEC ref ';'
        | ';'
	;
*/
step	: have_thus term labels by_just ';'
	| have_thus term labels
	  PROOF
	  proof_tail
	| NOW labels
	  proof_tail
	| LET identlist BE term ';'
	| ASSUME term labels ';'
	| TAKE term ';'
	| CONSIDER identlist opttype SUCH THAT term labels by_just ';'
	| CONSIDER identlist opttype SUCH THAT term labels
	  PROOF
	  proof_tail
	| SET term labels ';'
	| CASES by_just ';'
          cases
	| EXEC ref ';'
        | ';'
	;
cases	: 
	| cases
	  CASE ';'
	  proof_tail
	| cases
	  SUPPOSE term labels ';'
	  proof_tail
	;
proof_tail
	: step
	  proof_tail
	| QED by_just ';'
	| END ';'
	;
opttype	: 
	| BEING term
	;
labels	: 
	| labels '[' ident ']'
	;
by_just	: 
	| BY reflist
        | FROM reflist
        | BY reflist FROM reflist
	;
reflist	: ref
	| reflist ',' ref
	;
ref	: refitem
	| ref refitem
	;
refitem
	: OTHER
	| '(' expr ')'
	| '[' expr ']'
	;
term	: termitem
	| term termitem
	;
termitem
	: OTHER
	| ','
	| '(' expr ')'
	;
expr	: 
	| expr expritem
	;
expritem
	: OTHER
	| ','
	| ';'
	| '(' expr ')'
	| '[' expr ']'
	;
identlist
	: ident
	| identlist ident
	;
ident	: OTHER
	;
have_thus
	: 
	| THUS
	;
%%
#include <stdio.h>
/* int yylineno = 1; */
extern char *yytext;
extern int yylex();
extern int yyparse();
int main() { (void) yyparse(); return 0; }
int yywrap() { return 1; }
int yyerror(s) char *s;
{
  (void) fprintf(stderr, "%d: %s: unexpected \"%s\"\n", yylineno, s, yytext);
  return 0;
}
