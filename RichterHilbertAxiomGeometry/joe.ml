interactive_proof `; 
    intro_TAC ∀α u C, H1;
    consider X such that 
    X = topspace α [Xdef] by fol;
    topspace (subtopology α u) = u [uTop] by fol H1 Xdef TopspaceSubtopology;
    (closed_in (subtopology α u) C ⇔ C ⊂ u ∧ open_in (subtopology α u) (u DIFF C)) ∧ 
    ∀D. closed_in α D ⇔ D ⊂ X  ∧ open_in α (X DIFF D) [] by fol uTop Xdef USEclosed_in;
    simplify - uTop  H1 OpenInSubtopology GSYM Xdef;
    eq_tac [Left] 
    proof
      rewrite IMP_CONJ;
      intro_TAC Cu;
      rewrite  LEFT_IMP_EXISTS_THM;
      intro_TAC ∀t, tOpen u_Ctu;
      exists_TAC X DIFF t;
      u ⊂ X ∧ t ⊂ X [utX] by fol H1 Xdef tOpen OpenInSubset;
      simplify DIFF_REFL utX SUBSET_DIFF tOpen;
      set utX u_Ctu Cu -;
    qed;
    rewrite LEFT_IMP_EXISTS_THM IMP_CONJ;
    intro_TAC ∀D, DX, openX_D, C_Du;
    rewrite C_Du INTER_SUBSET;
    exists_TAC X DIFF D;
    rewrite openX_D;
    set H1 GSYM Xdef; `;;
