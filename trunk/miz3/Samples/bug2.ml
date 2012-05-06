let FOO = thm `;
  let P be num->bool;
  assume !x. P x \/ ~P x;
  thus (~ ~ ?x. P x) ==> ?x. P x;
`;;
