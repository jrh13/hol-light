/* This is my first try to write a certificate generator, borrows from
   examples in the cddlib-distribution LS */

#include "setoper.h"
#include "cdd.h"

void nocontra() {
  printf("No Contradiction\n");
  return;
}

void printsol(dd_LPSolutionPtr lps) {
  dd_colrange j;
  for (j=1; j<lps->d; j++) {
    dd_WriteNumber(stdout,lps->sol[j]);
  }
  printf("\n");
  return;
}

int main(int argc, char *argv[])
{        
  dd_ErrorType err=dd_NoError;
  dd_LPSolverType solver=dd_DualSimplex; 

  dd_LPPtr lp;
  
  dd_LPSolutionPtr lps;
  
  dd_MatrixPtr M;

  int found_contradiction=0;

  dd_set_global_constants();
  
  
  /* Input an LP using the cdd library  */
  
  if (err!=dd_NoError) goto _Err;
  M=dd_PolyFile2Matrix(stdin, &err);
  if (err!=dd_NoError) goto _Err;
  
  lp=dd_Matrix2LP(M, &err);
  if (err!=dd_NoError) goto _Err;
  
  /* Solve the LP */
  
  dd_LPSolve(lp, solver, &err);  /* Solve the LP */
  if (err!=dd_NoError) goto _Err;
  
  
  /* process solution */
  
  lps=dd_CopyLPSolution(lp);
  
  switch (lps->LPS) {
  case dd_Optimal:
    found_contradiction=dd_EqualToZero(lps->optvalue)?1:0;
    break;
    
  case dd_DualInconsistent:
  case dd_StrucDualInconsistent:
    found_contradiction=1;
    break;
    
  case dd_Inconsistent:
  case dd_StrucInconsistent:
    
  default:
    nocontra();
  }
  
  if (found_contradiction) {
    printsol(lps);
  } else {
    nocontra();
  }

  /* free allocated space */
  dd_FreeLPSolution(lps);
  dd_FreeLPData(lp);
  dd_FreeMatrix(M);

  return 0;
  
 _Err:;
  if (err!=dd_NoError) dd_WriteErrorMessages(stdout, err);
  return 1;
}



