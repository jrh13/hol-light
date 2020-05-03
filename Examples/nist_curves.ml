(* ========================================================================= *)
(* The NIST-recommended elliptic curves over prime-order finite fields.      *)
(* ========================================================================= *)

needs "Library/pocklington.ml";;
needs "Library/grouptheory.ml";;
needs "Library/ringtheory.ml";;

(* ------------------------------------------------------------------------- *)
(* The curve parameters, copied from the NIST FIPS 186-3 document.           *)
(* ------------------------------------------------------------------------- *)

(*** Taken from the document here just by naive copying modulo formatting
https://csrc.nist.gov/csrc/media/publications/fips/186/3/archive/2009-06-25/documents/fips_186-3.pdf
 *** The generators are paired up into ":(int#int)option" to suit our development
 *** The SEED_nnn values play no role in our development here
 ***)

(*** p192 ***)

let p_192 = new_definition `p_192 = 6277101735386680763835789423207666416083908700390324961279`;;
let n_192 = new_definition `n_192 = 6277101735386680763835789423176059013767194773182842284081`;;
let SEED_192 = new_definition `SEED_192 = 0x3045ae6fc8422f64ed579528d38120eae12196d5`;;
let c_192 = new_definition `c_192 = 0x3099d2bbbfcb2538542dcd5fb078b6ef5f3d6fe2c745de65`;;
let b_192 = new_definition `b_192 = 0x64210519e59c80e70fa7e9ab72243049feb8deecc146b9b1`;;
let G_192 = new_definition `G_192 = SOME(&0x188da80eb03090f67cbf20eb43a18800f4ff0afd82ff1012:int,&0x07192b95ffc8da78631011ed6b24cdd573f977a11e794811:int)`;;

(*** p224 ****)

let p_224 = new_definition `p_224 = 26959946667150639794667015087019630673557916260026308143510066298881`;;
let n_224 = new_definition `n_224 = 26959946667150639794667015087019625940457807714424391721682722368061`;;
let SEED_224 = new_definition `SEED_224 = 0xbd71344799d5c7fcdc45b59fa3b9ab8f6a948bc5`;;
let c_224 = new_definition `c_224 = 0x5b056c7e11dd68f40469ee7f3c7a7d74f7d121116506d031218291fb`;;
let b_224 = new_definition `b_224 = 0xb4050a850c04b3abf54132565044b0b7d7bfd8ba270b39432355ffb4`;;
let G_224 = new_definition `G_224 = SOME(&0xb70e0cbd6bb4bf7f321390b94a03c1d356c21122343280d6115c1d21:int,&0xbd376388b5f723fb4c22dfe6cd4375a05a07476444d5819985007e34:int)`;;

(**** p256 ****)

let p_256 = new_definition `p_256 = 115792089210356248762697446949407573530086143415290314195533631308867097853951`;;
let n_256 = new_definition `n_256 = 115792089210356248762697446949407573529996955224135760342422259061068512044369`;;
let SEED_256 = new_definition `SEED_256 = 0xc49d360886e704936a6678e1139d26b7819f7e90`;;
let c_256 = new_definition `c_256 = 0x7efba1662985be9403cb055c75d4f7e0ce8d84a9c5114abcaf3177680104fa0d`;;
let b_256 = new_definition `b_256 = 0x5ac635d8aa3a93e7b3ebbd55769886bc651d06b0cc53b0f63bce3c3e27d2604b`;;
let G_256 = new_definition `G_256 = SOME(&0x6b17d1f2e12c4247f8bce6e563a440f277037d812deb33a0f4a13945d898c296:int,&0x4fe342e2fe1a7f9b8ee7eb4a7c0f9e162bce33576b315ececbb6406837bf51f5:int)`;;

(**** p384 ****)

let p_384 = new_definition `p_384 = 39402006196394479212279040100143613805079739270465446667948293404245721771496870329047266088258938001861606973112319`;;
let n_384 = new_definition `n_384 = 39402006196394479212279040100143613805079739270465446667946905279627659399113263569398956308152294913554433653942643`;;
let SEED_384 = new_definition `SEED_384 = 0xa335926aa319a27a1d00896a6773a4827acdac73`;;
let c_384 = new_definition `c_384 = 0x79d1e655f868f02fff48dcdee14151ddb80643c1406d0ca10dfe6fc52009540a495e8042ea5f744f6e184667cc722483`;;
let b_384 = new_definition `b_384 = 0xb3312fa7e23ee7e4988e056be3f82d19181d9c6efe8141120314088f5013875ac656398d8a2ed19d2a85c8edd3ec2aef`;;
let G_384 = new_definition `G_384 = SOME(&0xaa87ca22be8b05378eb1c71ef320ad746e1d3b628ba79b9859f741e082542a385502f25dbf55296c3a545e3872760ab7:int,&0x3617de4a96262c6f5d9e98bf9292dc29f8f41dbd289a147ce9da3113b5f0b8c00a60b1ce1d7e819d7a431d7c90ea0e5f:int)`;;

(**** p521 ****)

let p_521 = new_definition `p_521 = 6864797660130609714981900799081393217269435300143305409394463459185543183397656052122559640661454554977296311391480858037121987999716643812574028291115057151`;;
let n_521 = new_definition `n_521 = 6864797660130609714981900799081393217269435300143305409394463459185543183397655394245057746333217197532963996371363321113864768612440380340372808892707005449`;;
let SEED_521 = new_definition `SEED_521 = 0xd09e8800291cb85396cc6717393284aaa0da64ba`;;
let c_521 = new_definition `c_521 = 0x0b48bfa5f420a34949539d2bdfc264eeeeb077688e44fbf0ad8f6d0edb37bd6b533281000518e19f1b9ffbe0fe9ed8a3c2200b8f875e523868c70c1e5bf55bad637`;;
let b_521 = new_definition `b_521 = 0x051953eb9618e1c9a1f929a21a0b68540eea2da725b99b315f3b8b489918ef109e156193951ec7e937b1652c0bd3bb1bf073573df883d2c34f1ef451fd46b503f00`;;
let G_521 = new_definition `G_521 = SOME(&0xc6858e06b70404e9cd9e3ecb662395b4429c648139053fb521f828af606b4d3dbaa14b5e77efe75928fe1dc127a2ffa8de3348b3c1856a429bf97e7e31c2e5bd66:int,&0x11839296a789a3bc0045c8a5fb42c7d1bd998f54449579b446817afbd17273e662c97ee72995ef42640c550b9013fad0761353c7086a272c24088be94769fd16650:int)`;;

(* ------------------------------------------------------------------------- *)
(* Expanded forms of the primes showing pseudo-Mersenne-ness.                *)
(* ------------------------------------------------------------------------- *)

let P_192 = prove
 (`p_192 = 2 EXP 192 - 2 EXP 64 - 1`,
  REWRITE_TAC[p_192] THEN CONV_TAC NUM_REDUCE_CONV);;

let P_224 = prove
 (`p_224 = 2 EXP 224 - 2 EXP 96 + 1`,
  REWRITE_TAC[p_224] THEN CONV_TAC NUM_REDUCE_CONV);;

let P_256 = prove
 (`p_256 = 2 EXP 256 - 2 EXP 224 + 2 EXP 192 + 2 EXP 96 - 1`,
  REWRITE_TAC[p_256] THEN CONV_TAC NUM_REDUCE_CONV);;

let P_384 = prove
 (`p_384 = 2 EXP 384 - 2 EXP 128 - 2 EXP 96 + 2 EXP 32 - 1`,
  REWRITE_TAC[p_384] THEN CONV_TAC NUM_REDUCE_CONV);;

let P_521 = prove
 (`p_521 = 2 EXP 521 - 1`,
  REWRITE_TAC[p_521] THEN CONV_TAC NUM_REDUCE_CONV);;

(* ------------------------------------------------------------------------- *)
(* Prove the the orders of the underlying fields and the orders of the       *)
(* elliptic curve groups themselves are indeed prime. The former is basic    *)
(* to the fact that we have a field, while the latter is useful to           *)
(* verify that the orders of the groups are actually what is claimed.        *)
(* To make this a bit faster and independent of external factorization       *)
(* tools, we first implement a variant of PRIME_CONV using a list of         *)
(* all necessary primes for the certification of the given prime: to         *)
(* certify p, need all primes q dividing p - 1, and so on recursively.       *)
(* ------------------------------------------------------------------------- *)

let guided_certify_prime hints =
  let rec guidedfactor n =
    if exists (fun p -> p =/ n) hints then [n] else
    let p = find (fun p -> mod_num n p =/ num_0) hints in
    p::(guidedfactor (quo_num n p)) in
  let rec cert_prime n =
    if n <=/ num_2 then
       if n =/ num_2 then Prime_2
       else failwith "certify_prime: not a prime!"
    else
      let m = n -/ num_1 in
      let pfact = guidedfactor m in
      let primes = setify_num pfact in
      let ms = map (fun d -> div_num m d) primes in
      let a = find_primitive_root m ms n in
      Primroot_and_factors((n,pfact),a,map (fun n -> n,cert_prime n) primes) in
  fun n -> if length(guidedfactor n) = 1 then cert_prime n
           else failwith "certify_prime: input is not a prime";;

let GUIDED_PROVE_PRIME hints = check_certificate o guided_certify_prime hints;;

let PRIME_RULE =
  let prime_tm = `prime` in
  fun hints tm0 ->
    let ptm,tm = dest_comb tm0 in
    if ptm <> prime_tm then failwith "expected term of form prime(n)" else
    let n = dest_numeral tm in
    GUIDED_PROVE_PRIME (map num_of_string hints @ [n]) n;;

let PRIME_P192 = time prove
 (`prime p_192`,
  REWRITE_TAC[p_192] THEN CONV_TAC NUM_REDUCE_CONV THEN
  (CONV_TAC o PRIME_RULE)
   ["2"; "3"; "5"; "7"; "11"; "17"; "19"; "23"; "29"; "31"; "37"; "41"; "43";
   "47"; "59"; "61"; "101"; "103"; "151"; "163"; "191"; "229"; "283"; "607";
   "619"; "631"; "907"; "2477"; "54251"; "149309"; "275729"; "379787";
   "723127"; "8413201"; "11393611"; "252396031"; "455827231987";
   "108341181769254293"; "5933177618131140283";
   "288626509448065367648032903"]);;

let PRIME_N192 = time prove
 (`prime n_192`,
  REWRITE_TAC[n_192] THEN CONV_TAC NUM_REDUCE_CONV THEN
  (CONV_TAC o PRIME_RULE)
  ["2"; "3"; "5"; "7"; "11"; "13"; "17"; "23"; "29"; "31"; "43"; "47"; "59";
   "61"; "71"; "73"; "103"; "199"; "239"; "331"; "439"; "547"; "569"; "881";
   "1031"; "1693"; "1889"; "2063"; "2389"; "4127"; "6829"; "51419"; "53197";
   "54623"; "60449"; "15716741"; "46245989"; "51920273"; "103840547";
   "7244839476697597"; "7532705587894727"; "9564682313913860059195669";
   "3433859179316188682119986911"]);;

let PRIME_P224 = time prove
 (`prime p_224`,
  REWRITE_TAC[p_224] THEN CONV_TAC NUM_REDUCE_CONV THEN
  (CONV_TAC o PRIME_RULE)
  ["2"; "3"; "5"; "7"; "11"; "17"; "23"; "31"; "43"; "47"; "173"; "257";
   "347"; "373"; "641"; "727"; "16657"; "17449"; "65537"; "166571"; "274177";
   "2998279"; "6700417"; "67280421310721"]);;

let PRIME_N224 = time prove
 (`prime n_224`,
  REWRITE_TAC[n_224] THEN CONV_TAC NUM_REDUCE_CONV THEN
  (CONV_TAC o PRIME_RULE)
  ["2"; "3"; "5"; "7"; "11"; "13"; "17"; "23"; "29"; "31"; "37"; "41"; "43";
   "47"; "61"; "67"; "89"; "101"; "127"; "139"; "173"; "239"; "269"; "347";
   "349"; "509"; "631"; "659"; "1303"; "1319"; "2089"; "2153"; "2707";
   "3433"; "10909"; "20599"; "30859"; "85999"; "87739"; "145091"; "166823";
   "11105363"; "13928737"; "821796863"; "432621809776543";
   "136401162692544977256234449"; "34646440928557194402992574983797";
   "375503554633724504423937478103159147573209";
   "50520606258875818707470860153287666700917696099933389351507"]);;

let PRIME_P256 = time prove
 (`prime p_256`,
  REWRITE_TAC[p_256] THEN CONV_TAC NUM_REDUCE_CONV THEN
  (CONV_TAC o PRIME_RULE)
  ["2"; "3"; "5"; "7"; "11"; "13"; "17"; "23"; "43"; "53"; "107"; "157";
   "173"; "181"; "197"; "241"; "257"; "313"; "641"; "661"; "727"; "757";
   "919"; "1087"; "1531"; "2411"; "3677"; "3769"; "4349"; "17449"; "18169";
   "65537"; "78283"; "490463"; "704251"; "6700417"; "204061199";
   "34282281433"; "66417393611"; "11290956913871"; "46076956964474543";
   "774023187263532362759620327192479577272145303";
   "835945042244614951780389953367877943453916927241"]);;

let PRIME_N256 = time prove
 (`prime n_256`,
  REWRITE_TAC[n_256] THEN CONV_TAC NUM_REDUCE_CONV THEN
  (CONV_TAC o PRIME_RULE)
  ["2"; "3"; "5"; "7"; "11"; "13"; "17"; "19"; "29"; "31"; "37"; "41"; "43";
   "71"; "97"; "127"; "131"; "151"; "229"; "263"; "311"; "337"; "373"; "727";
   "1201"; "1297"; "1511"; "3023"; "3407"; "9547"; "16879"; "17449"; "38189";
   "104471"; "126241"; "155317"; "3969899"; "9350987"; "187019741";
   "191039911"; "311245691"; "622491383"; "1002328039319";
   "208150935158385979"; "2624747550333869278416773953"]);;

let PRIME_P384 = time prove
 (`prime p_384`,
  REWRITE_TAC[p_384] THEN CONV_TAC NUM_REDUCE_CONV THEN
  (CONV_TAC o PRIME_RULE)
  ["2"; "3"; "5"; "7"; "11"; "13"; "17"; "19"; "23"; "29"; "41"; "43"; "47";
   "59"; "61"; "67"; "73"; "79"; "97"; "131"; "139"; "157"; "181"; "211";
   "233"; "263"; "271"; "293"; "599"; "661"; "881"; "937"; "1033"; "1373";
   "1579"; "2213"; "3253"; "3517"; "6317"; "8389"; "21407"; "38557";
   "312289"; "336757"; "363557"; "568151"; "6051631"; "105957871";
   "246608641"; "513928823"; "532247449"; "2862218959"; "53448597593";
   "807145746439"; "44925942675193"; "1357291859799823621";
   "529709925838459440593"; "35581458644053887931343";
   "23964610537191310276190549303"; "862725979338887169942859774909";
   "20705423504133292078628634597817";
   "413244619895455989650825325680172591660047";
   "12397338596863679689524759770405177749801411";
   "19173790298027098165721053155794528970226934547887232785722672956982046098136719667167519737147526097"]);;

let PRIME_N384 = time prove
 (`prime n_384`,
  REWRITE_TAC[n_384] THEN CONV_TAC NUM_REDUCE_CONV THEN
  (CONV_TAC o PRIME_RULE)
  ["2"; "3"; "5"; "7"; "11"; "13"; "17"; "19"; "23"; "29"; "31"; "37"; "41";
   "43"; "47"; "53"; "59"; "73"; "79"; "89"; "97"; "107"; "113"; "149";
   "151"; "163"; "173"; "179"; "181"; "233"; "251"; "311"; "347"; "421";
   "491"; "653"; "659"; "881"; "1087"; "1117"; "1553"; "3739"; "4349";
   "8699"; "16979"; "34429"; "37447"; "64901"; "248431"; "330563"; "455737";
   "1276987"; "8463023"; "9863677"; "154950581"; "272109983"; "290064143";
   "228572385721"; "1436833069313"; "23314383343543"; "37344768852931";
   "55942463741690639"; "426632512014427833817"; "120699720968197491947347";
   "1124679999981664229965379347"; "1495199339761412565498084319";
   "17942392077136950785977011829";
   "1059392654943455286185473617842338478315215895509773412096307";
   "3055465788140352002733946906144561090641249606160407884365391979704929268480326390471"]);;

let PRIME_P521 = time prove
 (`prime p_521`,
  REWRITE_TAC[p_521] THEN CONV_TAC NUM_REDUCE_CONV THEN
  (CONV_TAC o PRIME_RULE)
  ["2"; "3"; "5"; "7"; "11"; "13"; "17"; "19"; "23"; "29"; "31"; "37"; "41";
   "43"; "53"; "59"; "61"; "79"; "89"; "103"; "109"; "113"; "131"; "151";
   "157"; "173"; "179"; "223"; "227"; "257"; "277"; "317"; "347"; "397";
   "521"; "683"; "1051"; "1237"; "1381"; "1433"; "1613"; "1663"; "2437";
   "2731"; "3191"; "8191"; "23609"; "28793"; "42641"; "49481"; "51481";
   "61681"; "409891"; "858001"; "2995763"; "5746001"; "7623851"; "8620289";
   "9211861"; "34110701"; "308761441"; "2400573761"; "2534364967";
   "24098228377"; "65427463921"; "674750394557"; "108140989558681";
   "145295143558111"; "361725589517273017"; "173308343918874810521923841"]);;

let PRIME_N521 = time prove
 (`prime n_521`,
  REWRITE_TAC[n_521] THEN CONV_TAC NUM_REDUCE_CONV THEN
  (CONV_TAC o PRIME_RULE)
  ["2"; "3"; "5"; "7"; "11"; "13"; "17"; "19"; "23"; "29"; "31"; "37"; "41";
   "47"; "53"; "59"; "61"; "71"; "73"; "79"; "97"; "109"; "113"; "127";
   "131"; "157"; "181"; "191"; "193"; "227"; "229"; "233"; "241"; "257";
   "263"; "277"; "281"; "311"; "421"; "547"; "593"; "641"; "659"; "811";
   "877"; "1187"; "1283"; "1543"; "5449"; "6043"; "9227"; "10861"; "14461";
   "15601"; "17293"; "17467"; "20341"; "65677"; "92581"; "133279"; "161969";
   "370471"; "495527"; "777241"; "6937379"; "8196883"; "10577321";
   "10924559"; "19353437"; "186406729"; "1458105463"; "101785224689";
   "43800962361397"; "60018716061994831"; "88599952463812275001";
   "3473195323567808068309"; "4239602065187190872179";
   "1647781915921980690468599"; "144471089338257942164514676806340723";
   "7427946019382605513260578233234962521";
   "15994076126984618329123851002118749004583184815459808099";
   "3636410625392624440351547907325502812950802686368714273274221490761556277859337865760708490235892541081304511";
   "3615194794881930010216942559103847593050265703173292383701371712350878926821661243755933835426896058418509759880171943"]);;

(* ------------------------------------------------------------------------- *)
(* Some basic sanity checks on the (otherwise unused) c parameter.           *)
(* ------------------------------------------------------------------------- *)

let SANITY_CHECK_192 = prove
 (`(&b_192 pow 2 * &c_192:int == -- &27) (mod &p_192)`,
  REWRITE_TAC[G_192; p_192; b_192; c_192] THEN
  REWRITE_TAC[GSYM INT_REM_EQ] THEN CONV_TAC INT_REDUCE_CONV);;

let SANITY_CHECK_224 = prove
 (`(&b_224 pow 2 * &c_224:int == -- &27) (mod &p_224)`,
  REWRITE_TAC[G_224; p_224; b_224; c_224] THEN
  REWRITE_TAC[GSYM INT_REM_EQ] THEN CONV_TAC INT_REDUCE_CONV);;

let SANITY_CHECK_256 = prove
 (`(&b_256 pow 2 * &c_256:int == -- &27) (mod &p_256)`,
  REWRITE_TAC[G_256; p_256; b_256; c_256] THEN
  REWRITE_TAC[GSYM INT_REM_EQ] THEN CONV_TAC INT_REDUCE_CONV);;

let SANITY_CHECK_384 = prove
 (`(&b_384 pow 2 * &c_384:int == -- &27) (mod &p_384)`,
  REWRITE_TAC[G_384; p_384; b_384; c_384] THEN
  REWRITE_TAC[GSYM INT_REM_EQ] THEN CONV_TAC INT_REDUCE_CONV);;

let SANITY_CHECK_521 = prove
 (`(&b_521 pow 2 * &c_521:int == -- &27) (mod &p_521)`,
  REWRITE_TAC[G_521; p_521; b_521; c_521] THEN
  REWRITE_TAC[GSYM INT_REM_EQ] THEN CONV_TAC INT_REDUCE_CONV);;

(* ------------------------------------------------------------------------- *)
(* The general notion of an elliptic curve, in the basic Weierstrass form.   *)
(* We use the option type to augment it with the "point at infinity" NONE.   *)
(* Follows Washington "Elliptic Curves, Number Theory and Cryptography" p14. *)
(*                                                                           *)
(*         y^2 = x^3 + a * x + b   over some field F                         *)
(*                                                                           *)
(* This isn't general enough for working over characteristics 2 and 3,       *)
(* but is more than enough for all the curves we are concerned with,         *)
(* where we always have a = -3 and using the integers modulo a large prime.  *)
(* ------------------------------------------------------------------------- *)

let weierstrass_point = define
 `(weierstrass_point f NONE <=> T) /\
  (weierstrass_point f (SOME(x:A,y)) <=>
        x IN ring_carrier f /\ y IN ring_carrier f)`;;

let weierstrass_curve = define
 `(weierstrass_curve(f:A ring,a:A,b:A) NONE <=> T) /\
  (weierstrass_curve(f:A ring,a:A,b:A) (SOME(x,y)) <=>
        x IN ring_carrier f /\ y IN ring_carrier f /\
        ring_pow f y 2 =
        ring_add f (ring_pow f x 3) (ring_add f (ring_mul f a x) b))`;;

let weierstrass_neg = define
 `(weierstrass_neg (f:A ring,a:A,b:A) NONE = NONE) /\
  (weierstrass_neg (f:A ring,a:A,b:A) (SOME(x:A,y)) = SOME(x,ring_neg f y))`;;

let weierstrass_add = define
 `(!y. weierstrass_add (f:A ring,a:A,b:A) NONE y = y) /\
  (!x. weierstrass_add (f:A ring,a:A,b:A) x NONE = x) /\
  (!x1 y1 x2 y2.
        weierstrass_add (f:A ring,a:A,b:A) (SOME(x1,y1)) (SOME(x2,y2)) =
        if x1 = x2 then
          if y1 = y2 /\ ~(y1 = ring_0 f) then
            let m = ring_div f
              (ring_add f (ring_mul f (ring_of_num f 3) (ring_pow f x1 2)) a)
              (ring_mul f (ring_of_num f 2) y1) in
            let x3 = ring_sub f (ring_pow f m 2)
                                (ring_mul f (ring_of_num f 2) x1) in
            let y3 = ring_sub f (ring_mul f m (ring_sub f x1 x3)) y1 in
            SOME(x3,y3)
          else NONE
        else
          let m = ring_div f (ring_sub f y2 y1) (ring_sub f x2 x1) in
          let x3 = ring_sub f (ring_pow f m 2)
                              (ring_add f x1 x2) in
          let y3 = ring_sub f (ring_mul f m (ring_sub f x1 x3)) y1 in
          SOME(x3,y3))`;;

let weierstrass_singular = define
 `weierstrass_singular (f:A ring,a:A,b:A) <=>
        ring_add f (ring_mul f (ring_of_num f 4) (ring_pow f a 3))
                   (ring_mul f (ring_of_num f 27) (ring_pow f b 2)) =
        ring_0 f`;;

let weierstrass_group = define
 `weierstrass_group (f:A ring,a:A,b:A) =
        group(weierstrass_curve(f,a,b),
              NONE,
              weierstrass_neg(f,a,b),
              weierstrass_add(f,a,b))`;;

let FINITE_QUADRATIC_CURVE = prove
 (`!(r:A ring) h.
        integral_domain r /\ FINITE(ring_carrier r)
        ==> FINITE {x,y | x IN ring_carrier r /\ y IN ring_carrier r /\
                          ring_pow r y 2 = h x} /\
            CARD {x,y | x IN ring_carrier r /\ y IN ring_carrier r /\
                        ring_pow r y 2 = h x}
            <= 2 * CARD(ring_carrier r)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN ONCE_REWRITE_TAC[MULT_SYM] THEN
  MATCH_MP_TAC FINITE_CARD_LE_SUBSET THEN
  EXISTS_TAC
   `UNIONS {{x,y | y | y IN ring_carrier r /\ ring_pow r y 2 = h x} |x|
            (x:A) IN ring_carrier r}` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[UNIONS_GSPEC; SUBSET; FORALL_PAIR_THM; IN_ELIM_PAIR_THM] THEN
    SET_TAC[];
    MATCH_MP_TAC FINITE_CARD_LE_UNIONS THEN ASM_REWRITE_TAC[LE_REFL]] THEN
  X_GEN_TAC `x:A` THEN DISCH_TAC THEN ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN
  MATCH_MP_TAC FINITE_CARD_LE_IMAGE THEN
  ONCE_REWRITE_TAC[TAUT `p /\ q <=> p /\ ~(p ==> ~q)`] THEN
  REWRITE_TAC[ARITH_RULE `~(n <= 2) <=> 3 <= n`; CHOOSE_SUBSET_EQ] THEN
  ASM_SIMP_TAC[FINITE_RESTRICT] THEN
  CONV_TAC(ONCE_DEPTH_CONV HAS_SIZE_CONV) THEN
  DISCH_THEN(CHOOSE_THEN (CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC)) THEN
  FIRST_X_ASSUM SUBST1_TAC THEN REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET] THEN
  MP_TAC(INTEGRAL_DOMAIN_RULE
   `!x y:A. integral_domain r
    ==> (ring_pow r x 2 = ring_pow r y 2 <=> x = y \/ x = ring_neg r y)`) THEN
  ASM_REWRITE_TAC[IN_ELIM_THM] THEN ASM METIS_TAC[]);;

let (FINITE_WEIERSTRASS_CURVE,CARD_BOUND_WEIERSTRASS_CURVE) =
 (CONJ_PAIR o prove)
 (`(!f a b:A. field f /\ FINITE(ring_carrier f)
              ==> FINITE(weierstrass_curve(f,a,b))) /\
   (!f a b:A. field f /\ FINITE(ring_carrier f)
              ==> CARD(weierstrass_curve(f,a,b))
                   <= 2 * CARD(ring_carrier f) + 1)`,
  REWRITE_TAC[AND_FORALL_THM] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[TAUT `(p ==> q) /\ (p ==> r) <=> p ==> q /\ r`] THEN
  STRIP_TAC THEN MATCH_MP_TAC FINITE_CARD_LE_SUBSET THEN EXISTS_TAC
   `IMAGE SOME
     {(x,y) | (x:A) IN ring_carrier f /\ y IN ring_carrier f /\
              ring_pow f y 2 =
              ring_add f (ring_pow f x 3) (ring_add f (ring_mul f a x) b)}
    UNION {NONE}` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[weierstrass_curve; SUBSET; FORALL_OPTION_THM;
      IN_UNION; IN_SING; IN_IMAGE; option_INJ; FORALL_PAIR_THM;
      IN_ELIM_PAIR_THM; UNWIND_THM1] THEN
    REWRITE_TAC[option_DISTINCT; IN_CROSS] THEN REWRITE_TAC[IN] THEN
    REWRITE_TAC[weierstrass_curve] THEN SIMP_TAC[IN];
    MATCH_MP_TAC FINITE_CARD_LE_UNION] THEN
  REWRITE_TAC[FINITE_SING; CARD_SING; LE_REFL] THEN
  MATCH_MP_TAC FINITE_CARD_LE_IMAGE THEN
  MATCH_MP_TAC FINITE_QUADRATIC_CURVE THEN
  ASM_SIMP_TAC[FIELD_IMP_INTEGRAL_DOMAIN]);;

(* ------------------------------------------------------------------------- *)
(* Some slightly ad-hoc tactics for field reasoning.                         *)
(* ------------------------------------------------------------------------- *)

let NOT_RING_CHAR_DIVIDES_TAC =
  let bops = list_mk_binop `( * ):num->num->num`
  and patcheck = can (term_match [] `~(ring_char r divides NUMERAL n)`) in
  W(fun (asl,w) ->
        if not (patcheck w) then failwith "NOT_RING_CHAR_DIVIDES_TAC" else
        let n = dest_numeral(rand(rand w)) in
        let ns = multifactor n in
        let ntm = bops(map mk_numeral ns) in
        SUBST1_TAC(SYM(NUM_REDUCE_CONV ntm))) THEN
  ASM_SIMP_TAC[RING_CHAR_DIVIDES_MUL];;

let weierstrass_carrier_tac =
  W(fun (asl,w) ->
        let vs = filter ((=) `:A` o type_of)
                        (union (frees w) (freesl (map (concl o snd) asl))) in
        let cjs = map (fun x -> vsubst[x,`x:A`] `(x:A) IN ring_carrier f`)
                      vs in
        if cjs = [] then ALL_TAC else
        SUBGOAL_THEN (list_mk_conj cjs) STRIP_ASSUME_TAC THENL
         [REPEAT CONJ_TAC THEN RING_CARRIER_TAC; ALL_TAC]);;

let weierstrass_rabinify_tac =
  let rabinowitsch_lemma = prove
   (`!x y:A. ~(x = y)
             ==> !r. field r /\ x IN ring_carrier r /\ y IN ring_carrier r
                      ==> ?z. z IN ring_carrier r /\
                              ring_mul r (ring_sub r x y) z = ring_1 r`,
    REPEAT STRIP_TAC THEN EXISTS_TAC `ring_inv r (ring_sub r x y):A` THEN
    ASM_SIMP_TAC[FIELD_MUL_RINV; RING_SUB_EQ_0; RING_INV; RING_SUB]) in
  REPEAT
   (FIRST_X_ASSUM(MP_TAC o ISPEC `f:A ring` o MATCH_MP rabinowitsch_lemma) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
      RING_CARRIER_TAC; STRIP_TAC]);;

let weierstrass_invelim_tac =
  let is_fieldinv = can (term_match [] `ring_inv f (x:A)`)
  and pth = prove
   (`!f t:A.
          field f
          ==> t IN ring_carrier f
              ==> ring_inv f t = ring_0 f /\ t = ring_0 f \/
                  (?z. z IN ring_carrier f /\
                       ring_inv f t = z /\ ring_mul f t z = ring_1 f)`,
    ONCE_REWRITE_TAC[TAUT `p /\ q /\ r <=> q /\ p /\ r`] THEN
    REPEAT STRIP_TAC THEN ASM_CASES_TAC `t:A = ring_0 f` THEN
    ASM_SIMP_TAC[RING_INV_0; UNWIND_THM1; FIELD_MUL_RINV; RING_INV]) in
  W(fun (asl,w) ->
        let ctms = sort free_in (find_terms is_fieldinv w) in
        if ctms = [] then failwith "weierstrass_invelim_tac" else
        FIRST_ASSUM(MP_TAC o ISPEC (rand(hd ctms)) o MATCH_MP pth) THEN
        ANTS_TAC THENL [RING_CARRIER_TAC; ALL_TAC] THEN
        DISCH_THEN(DISJ_CASES_THEN2
         (CONJUNCTS_THEN2 SUBST1_TAC MP_TAC)
         (CHOOSE_THEN(CONJUNCTS_THEN2 ASSUME_TAC
           (CONJUNCTS_THEN2 SUBST1_TAC MP_TAC)))));;

let weierstrass_field_tac =
  REWRITE_TAC[DE_MORGAN_THM] THEN
  REPEAT STRIP_TAC THEN
  TRY(MATCH_MP_TAC(MESON[] `(~(a = b) ==> F) ==> a = b`) THEN DISCH_TAC) THEN
  TRY(FIRST_ASSUM CONTR_TAC) THEN
  weierstrass_carrier_tac THEN
  ASM_REWRITE_TAC[] THEN
  weierstrass_rabinify_tac THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (can (find_term is_eq) o concl))) THEN
  REWRITE_TAC[ring_div] THEN
  REPEAT weierstrass_invelim_tac THEN
  W(fun (asl,w) ->
        let th = INTEGRAL_DOMAIN_RULE w in
        MATCH_ACCEPT_TAC th ORELSE MATCH_MP_TAC th) THEN
  ASM_SIMP_TAC[FIELD_IMP_INTEGRAL_DOMAIN] THEN
  REPEAT CONJ_TAC THEN TRY RING_CARRIER_TAC THEN
  NOT_RING_CHAR_DIVIDES_TAC;;

(* ------------------------------------------------------------------------- *)
(* Proof of the group properties. This is just done by algebraic brute       *)
(* force, and often with far from optimal assumptions about the              *)
(* characteristic. In particular we only prove associativity for the         *)
(* specific characteristics we care about here.                              *)
(* ------------------------------------------------------------------------- *)

let WEIERSTRASS_CURVE_IMP_POINT = prove
 (`!f a b p. weierstrass_curve(f,a,b) p ==> weierstrass_point f p`,
  REWRITE_TAC[FORALL_OPTION_THM; FORALL_PAIR_THM] THEN
  SIMP_TAC[weierstrass_curve; weierstrass_point]);;

let WEIERSTRASS_POINT_NEG = prove
 (`!(f:A ring) a b p.
        weierstrass_point f p
        ==> weierstrass_point f (weierstrass_neg (f,a,b) p)`,
  REWRITE_TAC[FORALL_OPTION_THM; FORALL_PAIR_THM] THEN
  SIMP_TAC[weierstrass_neg; weierstrass_point; RING_NEG]);;

let WEIERSTRASS_POINT_ADD = prove
 (`!(f:A ring) a b p q.
        a IN ring_carrier f /\ b IN ring_carrier f /\
        weierstrass_point f p /\ weierstrass_point f q
        ==> weierstrass_point f (weierstrass_add (f,a,b) p q)`,
  REWRITE_TAC[FORALL_OPTION_THM; FORALL_PAIR_THM] THEN
  SIMP_TAC[weierstrass_add; weierstrass_point; LET_DEF; LET_END_DEF] THEN
  REPEAT STRIP_TAC THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[weierstrass_point]) THEN
  REPEAT STRIP_TAC THEN RING_CARRIER_TAC);;

let WEIERSTRASS_CURVE_0 = prove
 (`!f a b:A. weierstrass_curve(f,a,b) NONE`,
  REWRITE_TAC[weierstrass_curve]);;

let WEIERSTRASS_CURVE_NEG = prove
 (`!f a (b:A) p.
        integral_domain f /\ a IN ring_carrier f /\ b IN ring_carrier f /\
        weierstrass_curve(f,a,b) p
        ==> weierstrass_curve(f,a,b) (weierstrass_neg (f,a,b) p)`,
  SIMP_TAC[FORALL_OPTION_THM; FORALL_PAIR_THM; RING_NEG;
              weierstrass_curve; weierstrass_neg] THEN
  REPEAT GEN_TAC THEN CONV_TAC INTEGRAL_DOMAIN_RULE);;

let WEIERSTRASS_CURVE_ADD = prove
 (`!f a (b:A) p q.
        field f /\ ~(ring_char f = 2) /\ ~(ring_char f = 3) /\
        a IN ring_carrier f /\ b IN ring_carrier f /\
        weierstrass_curve(f,a,b) p /\ weierstrass_curve(f,a,b) q
        ==> weierstrass_curve(f,a,b) (weierstrass_add (f,a,b) p q)`,
  REWRITE_TAC[MESON[RING_CHAR_DIVIDES_PRIME; PRIME_2; PRIME_CONV `prime 3`]
   `field f /\ ~(ring_char f = 2) /\ ~(ring_char f = 3) /\ P <=>
    field f /\ ~(ring_char f divides 2) /\ ~(ring_char f divides 3) /\ P`] THEN
  REPLICATE_TAC 3 GEN_TAC THEN
  SIMP_TAC[FORALL_OPTION_THM; FORALL_PAIR_THM; RING_ADD;
              weierstrass_curve; weierstrass_add] THEN
  MAP_EVERY X_GEN_TAC [`x1:A`; `y1:A`; `x2:A`; `y2:A`] THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[DE_MORGAN_THM]) THEN
  REPEAT(FIRST_X_ASSUM(DISJ_CASES_THEN ASSUME_TAC)) THEN
  REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC)) THEN
  REPEAT(FIRST_X_ASSUM SUBST_ALL_TAC) THEN
  REPEAT LET_TAC THEN REWRITE_TAC[weierstrass_curve] THEN
  REPEAT STRIP_TAC THEN TRY RING_CARRIER_TAC THEN
  weierstrass_field_tac);;

let WEIERSTRASS_ADD_LNEG = prove
 (`!f a (b:A) p.
        field f /\ ~(ring_char f = 2) /\
        a IN ring_carrier f /\ b IN ring_carrier f /\
        weierstrass_curve(f,a,b) p
        ==> weierstrass_add(f,a,b) (weierstrass_neg (f,a,b) p) p = NONE`,
  REWRITE_TAC[MESON[RING_CHAR_DIVIDES_PRIME; PRIME_2]
   `field f /\ ~(ring_char f = 2) /\ P <=>
    field f /\ ~(ring_char f divides 2) /\ P`] THEN
  REPLICATE_TAC 3 GEN_TAC THEN
  SIMP_TAC[FORALL_OPTION_THM; FORALL_PAIR_THM; RING_ADD;
              weierstrass_curve; weierstrass_neg; weierstrass_add] THEN
  MAP_EVERY X_GEN_TAC [`x:A`; `y:A`] THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[DE_MORGAN_THM]) THEN
  REPEAT(FIRST_X_ASSUM(DISJ_CASES_THEN ASSUME_TAC)) THEN
  REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC)) THEN
  REPEAT LET_TAC THEN REWRITE_TAC[option_DISTINCT] THEN
  REPEAT STRIP_TAC THEN TRY RING_CARRIER_TAC THEN
  weierstrass_field_tac);;

let WEIERSTRASS_ADD_SYM = prove
 (`!f a (b:A) p q.
        field f /\
        a IN ring_carrier f /\ b IN ring_carrier f /\
        weierstrass_curve(f,a,b) p /\ weierstrass_curve(f,a,b) q
        ==> weierstrass_add (f,a,b) p q = weierstrass_add (f,a,b) q p`,
  REPLICATE_TAC 3 GEN_TAC THEN
  SIMP_TAC[FORALL_OPTION_THM; FORALL_PAIR_THM; RING_ADD;
              weierstrass_curve; weierstrass_add] THEN
  MAP_EVERY X_GEN_TAC [`x1:A`; `y1:A`; `x2:A`; `y2:A`] THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[DE_MORGAN_THM]) THEN
  REPEAT(FIRST_X_ASSUM(DISJ_CASES_THEN ASSUME_TAC)) THEN
  REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC)) THEN
  REPEAT(FIRST_X_ASSUM SUBST_ALL_TAC) THEN
  REPEAT LET_TAC THEN
  REWRITE_TAC[option_DISTINCT; option_INJ; PAIR_EQ] THEN
  REPEAT STRIP_TAC THEN TRY RING_CARRIER_TAC THEN
  weierstrass_field_tac);;

let WEIERSTRASS_ADD_ASSOC = prove
 (`!f a (b:A) p q r.
        field f /\
        ring_char f IN {p_192, p_224, p_256, p_384, p_521} /\
        ~weierstrass_singular(f,a,b) /\
        a IN ring_carrier f /\ b IN ring_carrier f /\
        weierstrass_curve(f,a,b) p /\
        weierstrass_curve(f,a,b) q /\
        weierstrass_curve(f,a,b) r
        ==> weierstrass_add (f,a,b) p (weierstrass_add (f,a,b) q r) =
            weierstrass_add (f,a,b) (weierstrass_add (f,a,b) p q) r`,
  MAP_EVERY X_GEN_TAC [`f:A ring`; `z1:A`; `z2:A`] THEN
  REWRITE_TAC[FORALL_OPTION_THM; weierstrass_add] THEN MATCH_MP_TAC(METIS[]
   `!p:A#A->A.
        (!x y z. P x y z ==> P z y x) /\
        (!x y z. p x = p y /\ p z = p y ==> P x y z) /\
        (!x y z. p z = p x /\ ~(p y = p x) ==> P x y z) /\
        (!x y z. ~(p z = p x) /\ p y = p x ==> P x y z) /\
        (!x y z. ~(p x = p y) /\ ~(p x = p z) /\ ~(p y = p z) ==> P x y z)
        ==> !x y z. P x y z`) THEN
  EXISTS_TAC `FST:A#A->A` THEN REWRITE_TAC[FORALL_PAIR_THM] THEN CONJ_TAC THENL
   [REPEAT GEN_TAC THEN DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `~(ring_char(f:A ring) = 2) /\ ~(ring_char f = 3)`
    MP_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_INSERT]) THEN
      REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
      REWRITE_TAC[p_192; p_224; p_256; p_384; p_521] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;
      ASM_SIMP_TAC[WEIERSTRASS_ADD_SYM; WEIERSTRASS_CURVE_ADD]];
    ALL_TAC] THEN
  REWRITE_TAC[AND_FORALL_THM] THEN MAP_EVERY X_GEN_TAC
   [`x1:A`; `y1:A`; `x2:A`; `y2:A`; `x3:A`; `y3:A`] THEN
  SIMP_TAC[weierstrass_add] THEN REPEAT CONJ_TAC THEN STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM SUBST_ALL_TAC) THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[DE_MORGAN_THM]) THEN
  REPEAT(FIRST_X_ASSUM(DISJ_CASES_THEN ASSUME_TAC)) THEN
  REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC)) THEN
  REPEAT(FIRST_X_ASSUM SUBST_ALL_TAC) THEN
  REPEAT LET_TAC THEN REWRITE_TAC[weierstrass_add; weierstrass_curve] THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[DE_MORGAN_THM]) THEN
  REPEAT(FIRST_X_ASSUM(DISJ_CASES_THEN ASSUME_TAC)) THEN
  REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC)) THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check
    (fun th -> is_eq(concl th) && is_var(lhand(concl th)) &&
               (is_var(rand(concl th)) || is_ratconst(rand(concl th)))))) THEN
  REPEAT LET_TAC THEN
  REWRITE_TAC[option_DISTINCT; option_INJ; PAIR_EQ] THEN
  REPEAT STRIP_TAC THEN TRY RING_CARRIER_TAC THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check
    (fun th -> is_eq(concl th) && is_var(lhand(concl th)) &&
               (is_var(rand(concl th)) ||
                rand(concl th) = `ring_0 f:A`)))) THEN
  TRY(MATCH_MP_TAC(MESON[] `(~(a = b) ==> F) ==> a = b`) THEN DISCH_TAC) THEN
  TRY(FIRST_ASSUM CONTR_TAC) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[weierstrass_singular]) THEN
  weierstrass_field_tac THEN
  REWRITE_TAC[DE_MORGAN_THM] THEN REPEAT CONJ_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_INSERT]) THEN
  REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
  REWRITE_TAC[p_192; p_224; p_256; p_384; p_521] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(RAND_CONV DIVIDES_CONV) THEN REWRITE_TAC[]);;

let WEIERSTRASS_GROUP = prove
 (`!f a (b:A).
      field f /\
      ring_char f IN {p_192, p_224, p_256, p_384, p_521} /\
      a IN ring_carrier f /\ b IN ring_carrier f /\
      ~weierstrass_singular(f,a,b)
      ==> group_carrier(weierstrass_group(f,a,b)) = weierstrass_curve(f,a,b) /\
          group_id(weierstrass_group(f,a,b)) = NONE /\
          group_inv(weierstrass_group(f,a,b)) = weierstrass_neg(f,a,b) /\
          group_mul(weierstrass_group(f,a,b)) = weierstrass_add(f,a,b)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(ring_char(f:A ring) = 2) /\ ~(ring_char f = 3)`
  STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_INSERT]) THEN
    REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
    REWRITE_TAC[p_192; p_224; p_256; p_384; p_521] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  REWRITE_TAC[group_carrier; group_id; group_inv; group_mul; GSYM PAIR_EQ] THEN
  REWRITE_TAC[weierstrass_group; GSYM(CONJUNCT2 group_tybij)] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[IN; weierstrass_curve];
    REWRITE_TAC[IN] THEN
    ASM_SIMP_TAC[WEIERSTRASS_CURVE_NEG; FIELD_IMP_INTEGRAL_DOMAIN];
    REWRITE_TAC[IN] THEN ASM_SIMP_TAC[WEIERSTRASS_CURVE_ADD];
    REWRITE_TAC[IN] THEN ASM_SIMP_TAC[WEIERSTRASS_ADD_ASSOC];
    REWRITE_TAC[FORALL_OPTION_THM; FORALL_PAIR_THM; weierstrass_add];
    REWRITE_TAC[IN] THEN GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC(MESON[]
     `x = a /\ x = y ==> x = a /\ y = a`) THEN
    CONJ_TAC THENL
     [ASM_SIMP_TAC[WEIERSTRASS_ADD_LNEG];
      MATCH_MP_TAC WEIERSTRASS_ADD_SYM THEN
      ASM_SIMP_TAC[WEIERSTRASS_CURVE_NEG; FIELD_IMP_INTEGRAL_DOMAIN]]]);;


(* ------------------------------------------------------------------------- *)
(* Projective coordinates, (x,y,z) |-> (x/z,y/z) and (0,1,0) |-> infinity    *)
(* ------------------------------------------------------------------------- *)

let projective_point = define
 `projective_point f (x,y,z) <=>
        x IN ring_carrier f /\ y IN ring_carrier f /\ z IN ring_carrier f`;;

let projective_curve = define
 `projective_curve (f,a:A,b) (x,y,z) <=>
        x IN ring_carrier f /\
        y IN ring_carrier f /\
        z IN ring_carrier f /\
        ring_mul f (ring_pow f y 2) z =
        ring_add f (ring_pow f x 3)
                   (ring_add f (ring_mul f a (ring_mul f x (ring_pow f z 2)))
                               (ring_mul f b (ring_pow f z 3)))`;;

let weierstrass_of_projective = define
 `weierstrass_of_projective (f:A ring) (x,y,z) =
        if z = ring_0 f then NONE
        else SOME(ring_div f x z,ring_div f y z)`;;

let projective_of_weierstrass = define
 `projective_of_weierstrass (f:A ring) NONE = (ring_0 f,ring_1 f,ring_0 f) /\
  projective_of_weierstrass f (SOME(x,y)) = (x,y,ring_1 f)`;;

let projective_eq = define
 `projective_eq (f:A ring) (x,y,z) (x',y',z') <=>
        (z = ring_0 f <=> z' = ring_0 f) /\
        ring_mul f x z' = ring_mul f x' z /\
        ring_mul f y z' = ring_mul f y' z`;;

let projective_0 = new_definition
 `projective_0 (f:A ring,a:A,b:A) = (ring_0 f,ring_1 f,ring_0 f)`;;

let projective_neg = new_definition
 `projective_neg (f,a:A,b:A) (x,y,z) = (x:A,ring_neg f y:A,z:A)`;;

let projective_add = new_definition
 `projective_add (f,a,b) (x1,y1,z1) (x2,y2,z2) =
    if z1 = ring_0 f then (x2,y2,z2)
    else if z2 = ring_0 f then (x1,y1,z1)
    else if projective_eq f (x1,y1,z1) (x2,y2,z2) then
      let t =
          ring_add f (ring_mul f a (ring_pow f z1 2))
          (ring_mul f (ring_of_num f 3) (ring_pow f x1 2))
      and u = ring_mul f y1 z1 in
      let v = ring_mul f u (ring_mul f x1 y1) in
      let w = ring_sub f (ring_pow f t 2) (ring_mul f (ring_of_num f 8) v) in
      (ring_mul f (ring_of_num f 2) (ring_mul f u w),
       ring_sub f (ring_mul f t (ring_sub f (ring_mul f (ring_of_num f 4) v) w))
       (ring_mul f (ring_of_num f 8)
       (ring_mul f (ring_pow f y1 2) (ring_pow f u 2))),
       ring_mul f (ring_of_num f 8) (ring_pow f u 3))
    else if projective_eq f (projective_neg (f,a,b) (x1,y1,z1)) (x2,y2,z2) then
      projective_0 (f,a,b)
    else
      let u = ring_sub f (ring_mul f y2 z1) (ring_mul f y1 z2)
      and v = ring_sub f (ring_mul f x2 z1) (ring_mul f x1 z2) in
      let w =
          ring_sub f
          (ring_sub f (ring_mul f (ring_pow f u 2) (ring_mul f z1 z2))
          (ring_pow f v 3))
          (ring_mul f (ring_of_num f 2)
          (ring_mul f (ring_pow f v 2) (ring_mul f x1 z2))) in
      (ring_mul f v w,
       ring_sub f
       (ring_mul f u
       (ring_sub f (ring_mul f (ring_pow f v 2) (ring_mul f x1 z2)) w))
       (ring_mul f (ring_pow f v 3) (ring_mul f y1 z2)),
       ring_mul f (ring_pow f v 3) (ring_mul f z1 z2))`;;

let PROJECTIVE_CURVE_IMP_POINT = prove
 (`!f a b p. projective_curve(f,a,b) p ==> projective_point f p`,
  REWRITE_TAC[FORALL_OPTION_THM; FORALL_PAIR_THM] THEN
  SIMP_TAC[projective_curve; projective_point]);;

let PROJECTIVE_OF_WEIERSTRASS_POINT_EQ = prove
 (`!(f:A ring) p.
        projective_point f (projective_of_weierstrass f p) <=>
        weierstrass_point f p`,
  REWRITE_TAC[FORALL_OPTION_THM; FORALL_PAIR_THM] THEN
  REWRITE_TAC[weierstrass_point; projective_of_weierstrass] THEN
  SIMP_TAC[projective_point; RING_0; RING_1]);;

let PROJECTIVE_OF_WEIERSTRASS_POINT = prove
 (`!(f:A ring) p.
        weierstrass_point f p
        ==> projective_point f (projective_of_weierstrass f p)`,
  REWRITE_TAC[PROJECTIVE_OF_WEIERSTRASS_POINT_EQ]);;

let WEIERSTRASS_OF_PROJECTIVE_POINT = prove
 (`!(f:A ring) p.
        projective_point f p
        ==> weierstrass_point f (weierstrass_of_projective f p)`,
  SIMP_TAC[FORALL_PAIR_THM; weierstrass_of_projective; projective_point] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC[weierstrass_point; RING_DIV]);;

let PROJECTIVE_OF_WEIERSTRASS_EQ = prove
 (`!(f:A ring) p q.
        field f
        ==> (projective_of_weierstrass f p = projective_of_weierstrass f q <=>
             p = q)`,
  REWRITE_TAC[FORALL_OPTION_THM; FORALL_PAIR_THM; field] THEN
  REWRITE_TAC[projective_of_weierstrass; option_DISTINCT; option_INJ] THEN
  SIMP_TAC[PAIR_EQ]);;

let WEIERSTRASS_OF_PROJECTIVE_EQ = prove
 (`!(f:A ring) p q.
        field f /\ projective_point f p /\ projective_point f q
        ==> (weierstrass_of_projective f p = weierstrass_of_projective f q <=>
             projective_eq f p q)`,
  REWRITE_TAC[FORALL_PAIR_THM; projective_point] THEN
  REWRITE_TAC[weierstrass_of_projective; projective_eq] THEN
  REPEAT STRIP_TAC THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[option_INJ; option_DISTINCT]) THEN
  ASM_SIMP_TAC[RING_MUL_RZERO; PAIR_EQ] THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ_ALT]
   (REWRITE_RULE[CONJ_ASSOC] FIELD_MUL_LINV)))) THEN
  ASM_REWRITE_TAC[ring_div] THEN
  W(MATCH_MP_TAC o INTEGRAL_DOMAIN_RULE o snd) THEN
  ASM_SIMP_TAC[RING_INV; FIELD_IMP_INTEGRAL_DOMAIN]);;

let WEIERSTRASS_OF_PROJECTIVE_OF_WEIERSTRASS = prove
 (`!(f:A ring) p.
        field f /\ weierstrass_point f p
        ==> weierstrass_of_projective f (projective_of_weierstrass f p) = p`,
  REWRITE_TAC[FORALL_OPTION_THM; FORALL_PAIR_THM; field] THEN
  SIMP_TAC[weierstrass_of_projective; projective_of_weierstrass;
           weierstrass_point; RING_DIV_1]);;

let PROJECTIVE_OF_WEIERSTRASS_OF_PROJECTIVE = prove
 (`!(f:A ring) p.
        field f /\ projective_point f p
        ==> projective_eq f
             (projective_of_weierstrass f (weierstrass_of_projective f p)) p`,
  SIMP_TAC[GSYM WEIERSTRASS_OF_PROJECTIVE_EQ;
           WEIERSTRASS_OF_PROJECTIVE_OF_WEIERSTRASS;
           PROJECTIVE_OF_WEIERSTRASS_POINT_EQ;
           WEIERSTRASS_OF_PROJECTIVE_POINT]);;

let PROJECTIVE_OF_WEIERSTRASS_CURVE_EQ = prove
 (`!(f:A ring) a b p.
        field f /\ a IN ring_carrier f /\ b IN ring_carrier f /\
        weierstrass_point f p
        ==> (projective_curve (f,a,b) (projective_of_weierstrass f p) <=>
             weierstrass_curve (f,a,b) p)`,
  REWRITE_TAC[FORALL_OPTION_THM; FORALL_PAIR_THM; weierstrass_point] THEN
  REWRITE_TAC[weierstrass_curve; projective_of_weierstrass] THEN
  SIMP_TAC[projective_curve; RING_0; RING_1] THEN
  REPEAT STRIP_TAC THEN REPEAT(FIRST_X_ASSUM(MP_TAC o SYM)) THEN
  W(MATCH_MP_TAC o INTEGRAL_DOMAIN_RULE o snd) THEN
  ASM_SIMP_TAC[FIELD_IMP_INTEGRAL_DOMAIN]);;

let PROJECTIVE_OF_WEIERSTRASS_CURVE = prove
 (`!(f:A ring) a b p.
        field f /\ a IN ring_carrier f /\ b IN ring_carrier f /\
        weierstrass_curve (f,a,b) p
        ==> projective_curve (f,a,b) (projective_of_weierstrass f p)`,
  MESON_TAC[PROJECTIVE_OF_WEIERSTRASS_CURVE_EQ;
            WEIERSTRASS_CURVE_IMP_POINT]);;

let WEIERSTRASS_OF_PROJECTIVE_CURVE = prove
 (`!(f:A ring) a b p.
        field f /\ a IN ring_carrier f /\ b IN ring_carrier f /\
        projective_curve (f,a,b) p
        ==> weierstrass_curve (f,a,b) (weierstrass_of_projective f p)`,
  SIMP_TAC[FORALL_PAIR_THM; weierstrass_of_projective; projective_curve] THEN
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC[weierstrass_curve; RING_DIV] THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o SYM)) THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ_ALT]
   (REWRITE_RULE[CONJ_ASSOC] FIELD_MUL_LINV)))) THEN
  ASM_REWRITE_TAC[ring_div] THEN
  W(MATCH_MP_TAC o INTEGRAL_DOMAIN_RULE o snd) THEN
  ASM_SIMP_TAC[RING_INV; FIELD_IMP_INTEGRAL_DOMAIN]);;

let PROJECTIVE_POINT_NEG = prove
 (`!(f:A ring) a b p.
        field f /\ a IN ring_carrier f /\ b IN ring_carrier f /\
        projective_point f p
        ==> projective_point f (projective_neg (f,a,b) p)`,
  REWRITE_TAC[FORALL_PAIR_THM; projective_neg; projective_point] THEN
  REPEAT STRIP_TAC THEN TRY RING_CARRIER_TAC THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o SYM)) THEN
  W(MATCH_MP_TAC o INTEGRAL_DOMAIN_RULE o snd) THEN
  ASM_SIMP_TAC[FIELD_IMP_INTEGRAL_DOMAIN]);;

let PROJECTIVE_CURVE_NEG = prove
 (`!(f:A ring) a b p.
        field f /\ a IN ring_carrier f /\ b IN ring_carrier f /\
        projective_curve (f,a,b) p
        ==> projective_curve (f,a,b) (projective_neg (f,a,b) p)`,
  REWRITE_TAC[FORALL_PAIR_THM; projective_neg; projective_curve] THEN
  REPEAT STRIP_TAC THEN TRY RING_CARRIER_TAC THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o SYM)) THEN
  W(MATCH_MP_TAC o INTEGRAL_DOMAIN_RULE o snd) THEN
  ASM_SIMP_TAC[FIELD_IMP_INTEGRAL_DOMAIN]);;

let WEIERSTRASS_OF_PROJECTIVE_NEG = prove
 (`!(f:A ring) a b p.
        field f /\ a IN ring_carrier f /\ b IN ring_carrier f /\
        projective_point f p
        ==> weierstrass_of_projective f (projective_neg (f,a,b) p) =
            weierstrass_neg (f,a,b) (weierstrass_of_projective f p)`,
  REWRITE_TAC[FORALL_PAIR_THM; projective_neg; weierstrass_of_projective;
              projective_point] THEN
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[weierstrass_neg; option_INJ; PAIR_EQ] THEN
  weierstrass_field_tac);;

let PROJECTIVE_EQ_NEG = prove
 (`!(f:A ring) a b p p'.
        field f /\ a IN ring_carrier f /\ b IN ring_carrier f /\
        projective_point f p /\ projective_point f p' /\ projective_eq f p p'
        ==> projective_eq f
              (projective_neg (f,a,b) p) (projective_neg (f,a,b) p')`,
  REPEAT GEN_TAC THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  ASM_SIMP_TAC[GSYM WEIERSTRASS_OF_PROJECTIVE_EQ; PROJECTIVE_POINT_NEG] THEN
  ASM_SIMP_TAC[WEIERSTRASS_OF_PROJECTIVE_NEG]);;

let WEIERSTRASS_OF_PROJECTIVE_NEG_OF_WEIERSTRASS = prove
 (`!(f:A ring) a b p.
        field f /\ a IN ring_carrier f /\ b IN ring_carrier f /\
        weierstrass_point f p
        ==> weierstrass_of_projective f
             (projective_neg (f,a,b) (projective_of_weierstrass f p)) =
            weierstrass_neg (f,a,b) p`,
  SIMP_TAC[WEIERSTRASS_OF_PROJECTIVE_NEG;
           PROJECTIVE_OF_WEIERSTRASS_POINT;
           WEIERSTRASS_OF_PROJECTIVE_OF_WEIERSTRASS]);;

let PROJECTIVE_OF_WEIERSTRASS_NEG = prove
 (`!(f:A ring) a b p.
        field f /\ a IN ring_carrier f /\ b IN ring_carrier f /\
        weierstrass_point f p
        ==> projective_eq f
             (projective_of_weierstrass f (weierstrass_neg (f,a,b) p))
             (projective_neg (f,a,b) (projective_of_weierstrass f p))`,
  SIMP_TAC[GSYM WEIERSTRASS_OF_PROJECTIVE_EQ;
           PROJECTIVE_OF_WEIERSTRASS_POINT;
           PROJECTIVE_POINT_NEG; WEIERSTRASS_POINT_NEG;
           WEIERSTRASS_OF_PROJECTIVE_NEG;
           WEIERSTRASS_OF_PROJECTIVE_OF_WEIERSTRASS]);;

let PROJECTIVE_POINT_ADD = prove
 (`!(f:A ring) a b p q.
        field f /\ a IN ring_carrier f /\ b IN ring_carrier f /\
        projective_point f p /\ projective_point f q
        ==> projective_point f (projective_add (f,a,b) p q)`,
  REWRITE_TAC[FORALL_PAIR_THM; projective_add; projective_point;
              projective_0; projective_eq; LET_DEF; LET_END_DEF] THEN
  REPEAT STRIP_TAC THEN TRY RING_CARRIER_TAC THEN
  REPEAT(COND_CASES_TAC THEN
   ASM_REWRITE_TAC[projective_add; projective_point;
              projective_eq; LET_DEF; LET_END_DEF]) THEN
  REPEAT STRIP_TAC THEN RING_CARRIER_TAC);;

let PROJECTIVE_CURVE_ADD = prove
 (`!(f:A ring) a b p q.
        field f /\ a IN ring_carrier f /\ b IN ring_carrier f /\
        projective_curve (f,a,b) p /\ projective_curve (f,a,b) q
        ==> projective_curve (f,a,b) (projective_add (f,a,b) p q)`,
  REWRITE_TAC[FORALL_PAIR_THM; projective_add; projective_curve;
              projective_0; projective_eq; LET_DEF; LET_END_DEF] THEN
  REPEAT STRIP_TAC THEN TRY RING_CARRIER_TAC THEN
  REPEAT(COND_CASES_TAC THEN
   ASM_REWRITE_TAC[projective_add; projective_curve;
              projective_eq; LET_DEF; LET_END_DEF]) THEN
  REPEAT STRIP_TAC THEN TRY RING_CARRIER_TAC THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o SYM)) THEN
  W(MATCH_MP_TAC o INTEGRAL_DOMAIN_RULE o snd) THEN
  ASM_SIMP_TAC[FIELD_IMP_INTEGRAL_DOMAIN]);;

let WEIERSTRASS_OF_PROJECTIVE_ADD = prove
 (`!(f:A ring) a b p q.
        field f /\ ~(ring_char f = 2) /\ ~(ring_char f = 3) /\
        a IN ring_carrier f /\ b IN ring_carrier f /\
        projective_point f p /\ projective_point f q
        ==> weierstrass_of_projective f (projective_add (f,a,b) p q) =
            weierstrass_add (f,a,b)
             (weierstrass_of_projective f p)
             (weierstrass_of_projective f q)`,
  REWRITE_TAC[MESON[RING_CHAR_DIVIDES_PRIME; PRIME_2; PRIME_CONV `prime 3`]
   `field f /\ ~(ring_char f = 2) /\ ~(ring_char f = 3) /\ P <=>
    field f /\ ~(ring_char f divides 2) /\ ~(ring_char f divides 3) /\ P`] THEN
  REWRITE_TAC[FORALL_PAIR_THM; projective_point] THEN
  MAP_EVERY X_GEN_TAC
   [`f:A ring`; `a:A`; `b:A`; `x1:A`; `y1:A`; `z1:A`;
    `x2:A`; `y2:A`; `z2:A`] THEN
  STRIP_TAC THEN REWRITE_TAC[weierstrass_of_projective; projective_add] THEN
  MAP_EVERY ASM_CASES_TAC [`z1:A = ring_0 f`; `z2:A = ring_0 f`] THEN
  ASM_REWRITE_TAC[weierstrass_of_projective; weierstrass_add] THEN
  ASM_REWRITE_TAC[projective_eq; projective_neg; projective_0] THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  REPEAT LET_TAC THEN REWRITE_TAC[weierstrass_of_projective] THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
  REWRITE_TAC[option_DISTINCT; option_INJ; PAIR_EQ] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[DE_MORGAN_THM]) THEN
  REPEAT(FIRST_X_ASSUM(DISJ_CASES_TAC) ORELSE
         FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC)) THEN
  weierstrass_field_tac);;

let PROJECTIVE_EQ_ADD = prove
 (`!(f:A ring) a b p p' q q'.
        field f /\ ~(ring_char f = 2) /\ ~(ring_char f = 3) /\
        a IN ring_carrier f /\ b IN ring_carrier f /\
        projective_point f p /\ projective_point f p' /\
        projective_point f q /\ projective_point f q' /\
        projective_eq f p p' /\ projective_eq f q q'
        ==> projective_eq f
              (projective_add (f,a,b) p q) (projective_add (f,a,b) p' q')`,
  REPEAT GEN_TAC THEN
  REPLICATE_TAC 9 (DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  ASM_SIMP_TAC[GSYM WEIERSTRASS_OF_PROJECTIVE_EQ; PROJECTIVE_POINT_ADD] THEN
  ASM_SIMP_TAC[WEIERSTRASS_OF_PROJECTIVE_ADD]);;

let WEIERSTRASS_OF_PROJECTIVE_ADD_OF_WEIERSTRASS = prove
 (`!(f:A ring) a b p q.
        field f /\ ~(ring_char f = 2) /\ ~(ring_char f = 3) /\
        a IN ring_carrier f /\ b IN ring_carrier f /\
        weierstrass_point f p /\ weierstrass_point f q
        ==> weierstrass_of_projective f
             (projective_add (f,a,b)
               (projective_of_weierstrass f p)
               (projective_of_weierstrass f q)) =
            weierstrass_add (f,a,b) p q`,
  SIMP_TAC[WEIERSTRASS_OF_PROJECTIVE_ADD;
           PROJECTIVE_OF_WEIERSTRASS_POINT;
           WEIERSTRASS_OF_PROJECTIVE_OF_WEIERSTRASS]);;

let PROJECTIVE_OF_WEIERSTRASS_ADD = prove
 (`!(f:A ring) a b p q.
        field f /\ ~(ring_char f = 2) /\ ~(ring_char f = 3) /\
        a IN ring_carrier f /\ b IN ring_carrier f /\
        weierstrass_point f p /\ weierstrass_point f q
        ==> projective_eq f
             (projective_of_weierstrass f (weierstrass_add (f,a,b) p q))
             (projective_add (f,a,b)
               (projective_of_weierstrass f p)
               (projective_of_weierstrass f q))`,
  SIMP_TAC[GSYM WEIERSTRASS_OF_PROJECTIVE_EQ;
           PROJECTIVE_OF_WEIERSTRASS_POINT;
           PROJECTIVE_POINT_ADD; WEIERSTRASS_POINT_ADD;
           WEIERSTRASS_OF_PROJECTIVE_ADD;
           WEIERSTRASS_OF_PROJECTIVE_OF_WEIERSTRASS]);;

(* ------------------------------------------------------------------------- *)
(* Jacobian coordinates, (x,y,z) |-> (x/z^2,y/z^3) and (1,1,0) |-> infinity  *)
(* ------------------------------------------------------------------------- *)

let jacobian_point = define
 `jacobian_point f (x,y,z) <=>
        x IN ring_carrier f /\ y IN ring_carrier f /\ z IN ring_carrier f`;;

let jacobian_curve = define
 `jacobian_curve (f,a:A,b) (x,y,z) <=>
        x IN ring_carrier f /\
        y IN ring_carrier f /\
        z IN ring_carrier f /\
        ring_pow f y 2 =
        ring_add f (ring_pow f x 3)
                   (ring_add f (ring_mul f a (ring_mul f x (ring_pow f z 4)))
                               (ring_mul f b (ring_pow f z 6)))`;;

let weierstrass_of_jacobian = define
 `weierstrass_of_jacobian (f:A ring) (x,y,z) =
        if z = ring_0 f then NONE
        else SOME(ring_div f x (ring_pow f z 2),
                  ring_div f y (ring_pow f z 3))`;;

let jacobian_of_weierstrass = define
 `jacobian_of_weierstrass (f:A ring) NONE = (ring_1 f,ring_1 f,ring_0 f) /\
  jacobian_of_weierstrass f (SOME(x,y)) = (x,y,ring_1 f)`;;

let jacobian_eq = define
 `jacobian_eq (f:A ring) (x,y,z) (x',y',z') <=>
        (z = ring_0 f <=> z' = ring_0 f) /\
        ring_mul f x (ring_pow f z' 2) = ring_mul f x' (ring_pow f z 2) /\
        ring_mul f y (ring_pow f z' 3) = ring_mul f y' (ring_pow f z 3)`;;

let jacobian_0 = new_definition
 `jacobian_0 (f:A ring,a:A,b:A) = (ring_1 f,ring_1 f,ring_0 f)`;;

let jacobian_neg = new_definition
 `jacobian_neg (f,a:A,b:A) (x,y,z) = (x:A,ring_neg f y:A,z:A)`;;

let jacobian_add = new_definition
 `jacobian_add (f:A ring,a,b) (x1,y1,z1) (x2,y2,z2) =
   if z1 = ring_0 f then (x2,y2,z2)
   else if z2 = ring_0 f then (x1,y1,z1)
   else if jacobian_eq f (x1,y1,z1) (x2,y2,z2) then
     let v = ring_mul f (ring_of_num f 4) (ring_mul f x1 (ring_pow f y1 2))
     and w =
       ring_add f (ring_mul f (ring_of_num f 3) (ring_pow f x1 2))
       (ring_mul f a (ring_pow f z1 4)) in
     let x3 =
       ring_add f (ring_mul f (ring_neg f (ring_of_num f 2)) v)
       (ring_pow f w 2) in
     x3,
     ring_add f (ring_mul f (ring_neg f (ring_of_num f 8)) (ring_pow f y1 4))
     (ring_mul f (ring_sub f v x3) w),
     ring_mul f (ring_of_num f 2) (ring_mul f y1 z1)
    else if jacobian_eq f (jacobian_neg (f,a,b) (x1,y1,z1)) (x2,y2,z2) then
      jacobian_0 (f,a,b)
    else
     let r = ring_mul f x1 (ring_pow f z2 2)
     and s = ring_mul f x2 (ring_pow f z1 2)
     and t = ring_mul f y1 (ring_pow f z2 3)
     and u = ring_mul f y2 (ring_pow f z1 3) in
     let v = ring_sub f s r
     and w = ring_sub f u t in
     let x3 =
         ring_add f
         (ring_sub f (ring_neg f (ring_pow f v 3))
         (ring_mul f (ring_of_num f 2) (ring_mul f r (ring_pow f v 2))))
         (ring_pow f w 2) in
     x3,
     ring_add f (ring_mul f (ring_neg f t) (ring_pow f v 3))
     (ring_mul f (ring_sub f (ring_mul f r (ring_pow f v 2)) x3) w),
     ring_mul f v (ring_mul f z1 z2)`;;

let JACOBIAN_CURVE_IMP_POINT = prove
 (`!f a b p. jacobian_curve(f,a,b) p ==> jacobian_point f p`,
  REWRITE_TAC[FORALL_OPTION_THM; FORALL_PAIR_THM] THEN
  SIMP_TAC[jacobian_curve; jacobian_point]);;

let JACOBIAN_OF_WEIERSTRASS_POINT_EQ = prove
 (`!(f:A ring) p.
        jacobian_point f (jacobian_of_weierstrass f p) <=>
        weierstrass_point f p`,
  REWRITE_TAC[FORALL_OPTION_THM; FORALL_PAIR_THM] THEN
  REWRITE_TAC[weierstrass_point; jacobian_of_weierstrass] THEN
  SIMP_TAC[jacobian_point; RING_0; RING_1]);;

let JACOBIAN_OF_WEIERSTRASS_POINT = prove
 (`!(f:A ring) p.
        weierstrass_point f p
        ==> jacobian_point f (jacobian_of_weierstrass f p)`,
  REWRITE_TAC[JACOBIAN_OF_WEIERSTRASS_POINT_EQ]);;

let WEIERSTRASS_OF_JACOBIAN_POINT = prove
 (`!(f:A ring) p.
        jacobian_point f p
        ==> weierstrass_point f (weierstrass_of_jacobian f p)`,
  SIMP_TAC[FORALL_PAIR_THM; weierstrass_of_jacobian; jacobian_point] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC[weierstrass_point; RING_DIV; RING_POW]);;

let JACOBIAN_OF_WEIERSTRASS_EQ = prove
 (`!(f:A ring) p q.
        field f
        ==> (jacobian_of_weierstrass f p = jacobian_of_weierstrass f q <=>
             p = q)`,
  REWRITE_TAC[FORALL_OPTION_THM; FORALL_PAIR_THM; field] THEN
  REWRITE_TAC[jacobian_of_weierstrass; option_DISTINCT; option_INJ] THEN
  SIMP_TAC[PAIR_EQ]);;

let WEIERSTRASS_OF_JACOBIAN_EQ = prove
 (`!(f:A ring) p q.
        field f /\ jacobian_point f p /\ jacobian_point f q
        ==> (weierstrass_of_jacobian f p = weierstrass_of_jacobian f q <=>
             jacobian_eq f p q)`,
  REWRITE_TAC[FORALL_PAIR_THM; jacobian_point] THEN
  REWRITE_TAC[weierstrass_of_jacobian; jacobian_eq] THEN
  REPEAT STRIP_TAC THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[option_INJ; option_DISTINCT]) THEN
  ASM_SIMP_TAC[RING_MUL_RZERO; PAIR_EQ] THEN
  weierstrass_field_tac);;

let WEIERSTRASS_OF_JACOBIAN_OF_WEIERSTRASS = prove
 (`!(f:A ring) p.
        field f /\ weierstrass_point f p
        ==> weierstrass_of_jacobian f (jacobian_of_weierstrass f p) = p`,
  REWRITE_TAC[FORALL_OPTION_THM; FORALL_PAIR_THM; field] THEN
  SIMP_TAC[weierstrass_of_jacobian; jacobian_of_weierstrass;
           weierstrass_point; RING_POW_ONE; RING_DIV_1]);;

let JACOBIAN_OF_WEIERSTRASS_OF_JACOBIAN = prove
 (`!(f:A ring) p.
        field f /\ jacobian_point f p
        ==> jacobian_eq f
             (jacobian_of_weierstrass f (weierstrass_of_jacobian f p)) p`,
  SIMP_TAC[GSYM WEIERSTRASS_OF_JACOBIAN_EQ;
           WEIERSTRASS_OF_JACOBIAN_OF_WEIERSTRASS;
           JACOBIAN_OF_WEIERSTRASS_POINT_EQ;
           WEIERSTRASS_OF_JACOBIAN_POINT]);;

let JACOBIAN_OF_WEIERSTRASS_CURVE_EQ = prove
 (`!(f:A ring) a b p.
        field f /\ a IN ring_carrier f /\ b IN ring_carrier f /\
        weierstrass_point f p
        ==> (jacobian_curve (f,a,b) (jacobian_of_weierstrass f p) <=>
             weierstrass_curve (f,a,b) p)`,
  REWRITE_TAC[FORALL_OPTION_THM; FORALL_PAIR_THM; weierstrass_point] THEN
  REWRITE_TAC[weierstrass_curve; jacobian_of_weierstrass] THEN
  SIMP_TAC[jacobian_curve; RING_0; RING_1] THEN
  REPEAT STRIP_TAC THEN REPEAT(FIRST_X_ASSUM(MP_TAC o SYM)) THEN
  W(MATCH_MP_TAC o INTEGRAL_DOMAIN_RULE o snd) THEN
  ASM_SIMP_TAC[FIELD_IMP_INTEGRAL_DOMAIN]);;

let JACOBIAN_OF_WEIERSTRASS_CURVE = prove
 (`!(f:A ring) a b p.
        field f /\ a IN ring_carrier f /\ b IN ring_carrier f /\
        weierstrass_curve (f,a,b) p
        ==> jacobian_curve (f,a,b) (jacobian_of_weierstrass f p)`,
  MESON_TAC[JACOBIAN_OF_WEIERSTRASS_CURVE_EQ;
            WEIERSTRASS_CURVE_IMP_POINT]);;

let WEIERSTRASS_OF_JACOBIAN_CURVE = prove
 (`!(f:A ring) a b p.
        field f /\ a IN ring_carrier f /\ b IN ring_carrier f /\
        jacobian_curve (f,a,b) p
        ==> weierstrass_curve (f,a,b) (weierstrass_of_jacobian f p)`,
  SIMP_TAC[FORALL_PAIR_THM; weierstrass_of_jacobian; jacobian_curve] THEN
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC[weierstrass_curve; RING_DIV; RING_POW] THEN
  weierstrass_field_tac);;

let JACOBIAN_POINT_NEG = prove
 (`!(f:A ring) a b p.
        field f /\ a IN ring_carrier f /\ b IN ring_carrier f /\
        jacobian_point f p
        ==> jacobian_point f (jacobian_neg (f,a,b) p)`,
  REWRITE_TAC[FORALL_PAIR_THM; jacobian_neg; jacobian_point] THEN
  REPEAT STRIP_TAC THEN TRY RING_CARRIER_TAC THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o SYM)) THEN
  W(MATCH_MP_TAC o INTEGRAL_DOMAIN_RULE o snd) THEN
  ASM_SIMP_TAC[FIELD_IMP_INTEGRAL_DOMAIN]);;

let JACOBIAN_CURVE_NEG = prove
 (`!(f:A ring) a b p.
        field f /\ a IN ring_carrier f /\ b IN ring_carrier f /\
        jacobian_curve (f,a,b) p
        ==> jacobian_curve (f,a,b) (jacobian_neg (f,a,b) p)`,
  REWRITE_TAC[FORALL_PAIR_THM; jacobian_neg; jacobian_curve] THEN
  REPEAT STRIP_TAC THEN TRY RING_CARRIER_TAC THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o SYM)) THEN
  W(MATCH_MP_TAC o INTEGRAL_DOMAIN_RULE o snd) THEN
  ASM_SIMP_TAC[FIELD_IMP_INTEGRAL_DOMAIN]);;

let WEIERSTRASS_OF_JACOBIAN_NEG = prove
 (`!(f:A ring) a b p.
        field f /\ a IN ring_carrier f /\ b IN ring_carrier f /\
        jacobian_point f p
        ==> weierstrass_of_jacobian f (jacobian_neg (f,a,b) p) =
            weierstrass_neg (f,a,b) (weierstrass_of_jacobian f p)`,
  REWRITE_TAC[FORALL_PAIR_THM; jacobian_neg; weierstrass_of_jacobian;
              jacobian_point] THEN
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[weierstrass_neg; option_INJ; PAIR_EQ] THEN
  weierstrass_field_tac);;

let JACOBIAN_EQ_NEG = prove
 (`!(f:A ring) a b p p'.
        field f /\ a IN ring_carrier f /\ b IN ring_carrier f /\
        jacobian_point f p /\ jacobian_point f p' /\ jacobian_eq f p p'
        ==> jacobian_eq f
              (jacobian_neg (f,a,b) p) (jacobian_neg (f,a,b) p')`,
  REPEAT GEN_TAC THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  ASM_SIMP_TAC[GSYM WEIERSTRASS_OF_JACOBIAN_EQ; JACOBIAN_POINT_NEG] THEN
  ASM_SIMP_TAC[WEIERSTRASS_OF_JACOBIAN_NEG]);;

let WEIERSTRASS_OF_JACOBIAN_NEG_OF_WEIERSTRASS = prove
 (`!(f:A ring) a b p.
        field f /\ a IN ring_carrier f /\ b IN ring_carrier f /\
        weierstrass_point f p
        ==> weierstrass_of_jacobian f
             (jacobian_neg (f,a,b) (jacobian_of_weierstrass f p)) =
            weierstrass_neg (f,a,b) p`,
  SIMP_TAC[WEIERSTRASS_OF_JACOBIAN_NEG;
           JACOBIAN_OF_WEIERSTRASS_POINT;
           WEIERSTRASS_OF_JACOBIAN_OF_WEIERSTRASS]);;

let JACOBIAN_OF_WEIERSTRASS_NEG = prove
 (`!(f:A ring) a b p.
        field f /\ a IN ring_carrier f /\ b IN ring_carrier f /\
        weierstrass_point f p
        ==> jacobian_eq f
             (jacobian_of_weierstrass f (weierstrass_neg (f,a,b) p))
             (jacobian_neg (f,a,b) (jacobian_of_weierstrass f p))`,
  SIMP_TAC[GSYM WEIERSTRASS_OF_JACOBIAN_EQ;
           JACOBIAN_OF_WEIERSTRASS_POINT;
           JACOBIAN_POINT_NEG; WEIERSTRASS_POINT_NEG;
           WEIERSTRASS_OF_JACOBIAN_NEG;
           WEIERSTRASS_OF_JACOBIAN_OF_WEIERSTRASS]);;

let JACOBIAN_POINT_ADD = prove
 (`!(f:A ring) a b p q.
        field f /\ a IN ring_carrier f /\ b IN ring_carrier f /\
        jacobian_point f p /\ jacobian_point f q
        ==> jacobian_point f (jacobian_add (f,a,b) p q)`,
  REWRITE_TAC[FORALL_PAIR_THM; jacobian_add; jacobian_point;
              jacobian_0; jacobian_eq; LET_DEF; LET_END_DEF] THEN
  REPEAT STRIP_TAC THEN TRY RING_CARRIER_TAC THEN
  REPEAT(COND_CASES_TAC THEN
   ASM_REWRITE_TAC[jacobian_add; jacobian_point;
              jacobian_eq; LET_DEF; LET_END_DEF]) THEN
  REPEAT STRIP_TAC THEN RING_CARRIER_TAC);;

let JACOBIAN_CURVE_ADD = prove
 (`!(f:A ring) a b p q.
        field f /\ a IN ring_carrier f /\ b IN ring_carrier f /\
        jacobian_curve (f,a,b) p /\ jacobian_curve (f,a,b) q
        ==> jacobian_curve (f,a,b) (jacobian_add (f,a,b) p q)`,
  REWRITE_TAC[FORALL_PAIR_THM; jacobian_add; jacobian_curve;
              jacobian_0; jacobian_eq; LET_DEF; LET_END_DEF] THEN
  REPEAT STRIP_TAC THEN TRY RING_CARRIER_TAC THEN
  REPEAT(COND_CASES_TAC THEN
   ASM_REWRITE_TAC[jacobian_add; jacobian_curve;
              jacobian_eq; LET_DEF; LET_END_DEF]) THEN
  REPEAT STRIP_TAC THEN TRY RING_CARRIER_TAC THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o SYM)) THEN
  W(MATCH_MP_TAC o INTEGRAL_DOMAIN_RULE o snd) THEN
  ASM_SIMP_TAC[FIELD_IMP_INTEGRAL_DOMAIN]);;

let WEIERSTRASS_OF_JACOBIAN_ADD = prove
 (`!(f:A ring) a b p q.
        field f /\ ~(ring_char f = 2) /\ ~(ring_char f = 3) /\
        a IN ring_carrier f /\ b IN ring_carrier f /\
        jacobian_point f p /\ jacobian_point f q
        ==> weierstrass_of_jacobian f (jacobian_add (f,a,b) p q) =
            weierstrass_add (f,a,b)
             (weierstrass_of_jacobian f p)
             (weierstrass_of_jacobian f q)`,
  REWRITE_TAC[MESON[RING_CHAR_DIVIDES_PRIME; PRIME_2; PRIME_CONV `prime 3`]
   `field f /\ ~(ring_char f = 2) /\ ~(ring_char f = 3) /\ P <=>
    field f /\ ~(ring_char f divides 2) /\ ~(ring_char f divides 3) /\ P`] THEN
  REWRITE_TAC[FORALL_PAIR_THM; jacobian_point] THEN
  MAP_EVERY X_GEN_TAC
   [`f:A ring`; `a:A`; `b:A`; `x1:A`; `y1:A`; `z1:A`;
    `x2:A`; `y2:A`; `z2:A`] THEN
  STRIP_TAC THEN REWRITE_TAC[weierstrass_of_jacobian; jacobian_add] THEN
  MAP_EVERY ASM_CASES_TAC [`z1:A = ring_0 f`; `z2:A = ring_0 f`] THEN
  ASM_REWRITE_TAC[weierstrass_of_jacobian; weierstrass_add] THEN
  ASM_REWRITE_TAC[jacobian_eq; jacobian_neg; jacobian_0] THEN
  ASM_SIMP_TAC[ring_div; RING_INV_POW] THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  REPEAT LET_TAC THEN REWRITE_TAC[weierstrass_of_jacobian] THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
  REWRITE_TAC[option_DISTINCT; option_INJ; PAIR_EQ] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[DE_MORGAN_THM]) THEN
  REPEAT(FIRST_X_ASSUM(DISJ_CASES_TAC) ORELSE
         FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC)) THEN
  weierstrass_field_tac);;

let JACOBIAN_EQ_ADD = prove
 (`!(f:A ring) a b p p' q q'.
        field f /\ ~(ring_char f = 2) /\ ~(ring_char f = 3) /\
        a IN ring_carrier f /\ b IN ring_carrier f /\
        jacobian_point f p /\ jacobian_point f p' /\
        jacobian_point f q /\ jacobian_point f q' /\
        jacobian_eq f p p' /\ jacobian_eq f q q'
        ==> jacobian_eq f
              (jacobian_add (f,a,b) p q) (jacobian_add (f,a,b) p' q')`,
  REPEAT GEN_TAC THEN
  REPLICATE_TAC 9 (DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  ASM_SIMP_TAC[GSYM WEIERSTRASS_OF_JACOBIAN_EQ; JACOBIAN_POINT_ADD] THEN
  ASM_SIMP_TAC[WEIERSTRASS_OF_JACOBIAN_ADD]);;

let WEIERSTRASS_OF_JACOBIAN_ADD_OF_WEIERSTRASS = prove
 (`!(f:A ring) a b p q.
        field f /\ ~(ring_char f = 2) /\ ~(ring_char f = 3) /\
        a IN ring_carrier f /\ b IN ring_carrier f /\
        weierstrass_point f p /\ weierstrass_point f q
        ==> weierstrass_of_jacobian f
             (jacobian_add (f,a,b)
               (jacobian_of_weierstrass f p)
               (jacobian_of_weierstrass f q)) =
            weierstrass_add (f,a,b) p q`,
  SIMP_TAC[WEIERSTRASS_OF_JACOBIAN_ADD;
           JACOBIAN_OF_WEIERSTRASS_POINT;
           WEIERSTRASS_OF_JACOBIAN_OF_WEIERSTRASS]);;

let JACOBIAN_OF_WEIERSTRASS_ADD = prove
 (`!(f:A ring) a b p q.
        field f /\ ~(ring_char f = 2) /\ ~(ring_char f = 3) /\
        a IN ring_carrier f /\ b IN ring_carrier f /\
        weierstrass_point f p /\ weierstrass_point f q
        ==> jacobian_eq f
             (jacobian_of_weierstrass f (weierstrass_add (f,a,b) p q))
             (jacobian_add (f,a,b)
               (jacobian_of_weierstrass f p)
               (jacobian_of_weierstrass f q))`,
  SIMP_TAC[GSYM WEIERSTRASS_OF_JACOBIAN_EQ;
           JACOBIAN_OF_WEIERSTRASS_POINT;
           JACOBIAN_POINT_ADD; WEIERSTRASS_POINT_ADD;
           WEIERSTRASS_OF_JACOBIAN_ADD;
           WEIERSTRASS_OF_JACOBIAN_OF_WEIERSTRASS]);;

(* ------------------------------------------------------------------------- *)
(* Definition of the NIST curve groups and proof that they are groups.       *)
(* ------------------------------------------------------------------------- *)

let WEIERSTRASS_GROUP_REM = prove
 (`weierstrass_group(integer_mod_ring p,a rem &p,b) =
   weierstrass_group(integer_mod_ring p,a,b) /\
   weierstrass_curve(integer_mod_ring p,a rem &p,b) =
   weierstrass_curve(integer_mod_ring p,a,b) /\
   weierstrass_neg(integer_mod_ring p,a rem &p,b) =
   weierstrass_neg(integer_mod_ring p,a,b) /\
   weierstrass_add(integer_mod_ring p,a rem &p,b) =
   weierstrass_add(integer_mod_ring p,a,b)`,
  CONJ_TAC THENL
   [REWRITE_TAC[weierstrass_group] THEN AP_TERM_TAC; ALL_TAC] THEN
  REPEAT CONJ_TAC THEN
  REWRITE_TAC[PAIR_EQ; FUN_EQ_THM; FORALL_OPTION_THM; FORALL_PAIR_THM;
                weierstrass_curve; weierstrass_neg; weierstrass_add] THEN
  REWRITE_TAC[INTEGER_MOD_RING; INTEGER_MOD_RING_POW;
              INTEGER_MOD_RING_OF_NUM] THEN
  CONV_TAC INT_REM_DOWN_CONV THEN REWRITE_TAC[]);;

let p192_group = define
 `p192_group = weierstrass_group(integer_mod_ring p_192,--(&3),&b_192)`;;

let P192_GROUP = prove
 (`group_carrier p192_group =
     weierstrass_curve(integer_mod_ring p_192,--(&3),&b_192) /\
   group_id p192_group =
     NONE /\
   group_inv p192_group =
     weierstrass_neg(integer_mod_ring p_192,--(&3),&b_192) /\
   group_mul p192_group =
     weierstrass_add(integer_mod_ring p_192,--(&3),&b_192)`,
  REWRITE_TAC[p192_group] THEN
  ONCE_REWRITE_TAC[GSYM WEIERSTRASS_GROUP_REM] THEN
  MATCH_MP_TAC WEIERSTRASS_GROUP THEN
  REWRITE_TAC[FIELD_INTEGER_MOD_RING; INTEGER_MOD_RING_CHAR; PRIME_P192] THEN
  REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY; weierstrass_singular] THEN
  SIMP_TAC[p_192; b_192; INTEGER_MOD_RING; ARITH; IN_ELIM_THM;
           INTEGER_MOD_RING_POW; INTEGER_MOD_RING_OF_NUM] THEN
  CONV_TAC INT_REDUCE_CONV);;

let p224_group = define
 `p224_group = weierstrass_group(integer_mod_ring p_224,--(&3),&b_224)`;;

let P224_GROUP = prove
 (`group_carrier p224_group =
     weierstrass_curve(integer_mod_ring p_224,--(&3),&b_224) /\
   group_id p224_group =
     NONE /\
   group_inv p224_group =
     weierstrass_neg(integer_mod_ring p_224,--(&3),&b_224) /\
   group_mul p224_group =
     weierstrass_add(integer_mod_ring p_224,--(&3),&b_224)`,
  REWRITE_TAC[p224_group] THEN
  ONCE_REWRITE_TAC[GSYM WEIERSTRASS_GROUP_REM] THEN
  MATCH_MP_TAC WEIERSTRASS_GROUP THEN
  REWRITE_TAC[FIELD_INTEGER_MOD_RING; INTEGER_MOD_RING_CHAR; PRIME_P224] THEN
  REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY; weierstrass_singular] THEN
  SIMP_TAC[p_224; b_224; INTEGER_MOD_RING; ARITH; IN_ELIM_THM;
           INTEGER_MOD_RING_POW; INTEGER_MOD_RING_OF_NUM] THEN
  CONV_TAC INT_REDUCE_CONV);;

let p256_group = define
 `p256_group = weierstrass_group(integer_mod_ring p_256,--(&3),&b_256)`;;

let P256_GROUP = prove
 (`group_carrier p256_group =
     weierstrass_curve(integer_mod_ring p_256,--(&3),&b_256) /\
   group_id p256_group =
     NONE /\
   group_inv p256_group =
     weierstrass_neg(integer_mod_ring p_256,--(&3),&b_256) /\
   group_mul p256_group =
     weierstrass_add(integer_mod_ring p_256,--(&3),&b_256)`,
  REWRITE_TAC[p256_group] THEN
  ONCE_REWRITE_TAC[GSYM WEIERSTRASS_GROUP_REM] THEN
  MATCH_MP_TAC WEIERSTRASS_GROUP THEN
  REWRITE_TAC[FIELD_INTEGER_MOD_RING; INTEGER_MOD_RING_CHAR; PRIME_P256] THEN
  REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY; weierstrass_singular] THEN
  SIMP_TAC[p_256; b_256; INTEGER_MOD_RING; ARITH; IN_ELIM_THM;
           INTEGER_MOD_RING_POW; INTEGER_MOD_RING_OF_NUM] THEN
  CONV_TAC INT_REDUCE_CONV);;

let p384_group = define
 `p384_group = weierstrass_group(integer_mod_ring p_384,--(&3),&b_384)`;;

let P384_GROUP = prove
 (`group_carrier p384_group =
     weierstrass_curve(integer_mod_ring p_384,--(&3),&b_384) /\
   group_id p384_group =
     NONE /\
   group_inv p384_group =
     weierstrass_neg(integer_mod_ring p_384,--(&3),&b_384) /\
   group_mul p384_group =
     weierstrass_add(integer_mod_ring p_384,--(&3),&b_384)`,
  REWRITE_TAC[p384_group] THEN
  ONCE_REWRITE_TAC[GSYM WEIERSTRASS_GROUP_REM] THEN
  MATCH_MP_TAC WEIERSTRASS_GROUP THEN
  REWRITE_TAC[FIELD_INTEGER_MOD_RING; INTEGER_MOD_RING_CHAR; PRIME_P384] THEN
  REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY; weierstrass_singular] THEN
  SIMP_TAC[p_384; b_384; INTEGER_MOD_RING; ARITH; IN_ELIM_THM;
           INTEGER_MOD_RING_POW; INTEGER_MOD_RING_OF_NUM] THEN
  CONV_TAC INT_REDUCE_CONV);;

let p521_group = define
 `p521_group = weierstrass_group(integer_mod_ring p_521,--(&3),&b_521)`;;

let P521_GROUP = prove
 (`group_carrier p521_group =
     weierstrass_curve(integer_mod_ring p_521,--(&3),&b_521) /\
   group_id p521_group =
     NONE /\
   group_inv p521_group =
     weierstrass_neg(integer_mod_ring p_521,--(&3),&b_521) /\
   group_mul p521_group =
     weierstrass_add(integer_mod_ring p_521,--(&3),&b_521)`,
  REWRITE_TAC[p521_group] THEN
  ONCE_REWRITE_TAC[GSYM WEIERSTRASS_GROUP_REM] THEN
  MATCH_MP_TAC WEIERSTRASS_GROUP THEN
  REWRITE_TAC[FIELD_INTEGER_MOD_RING; INTEGER_MOD_RING_CHAR; PRIME_P521] THEN
  REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY; weierstrass_singular] THEN
  SIMP_TAC[p_521; b_521; INTEGER_MOD_RING; ARITH; IN_ELIM_THM;
           INTEGER_MOD_RING_POW; INTEGER_MOD_RING_OF_NUM] THEN
  CONV_TAC INT_REDUCE_CONV);;

(* ------------------------------------------------------------------------- *)
(* Prove, more or less by doing a gcd(x^p - x,x^3 + a * x + b) computation   *)
(* over F_p[x], that there are no solutions to the r.h.s. of the             *)
(* curve equations when the l.h.s. is 0. This implies that there are         *)
(* no 2-torsion points, since such points would necessarily have y = 0.      *)
(* ------------------------------------------------------------------------- *)

let num_modinv =
  let rec gcdex(m,n) =
    if n <=/ m then let (x,y) = gcdex(n,m) in (y,x)
    else if m =/ Int 0 then (Int 0,Int 1) else
    let q = quo_num n m in
    let r = n -/ q */ m in
    let (x,y) = gcdex(r,m) in (y -/ q */ x,x) in
  fun p n -> let (x,y) = gcdex(n,p) in
             if mod_num (x */ n) p =/ num_1 then mod_num x p
             else failwith "num_modinv";;

let EXCLUDE_ELLIPTIC_CURVE_ROOTS =
  let lemma_flt = prove
   (`((x pow 3 + a * x + b:int == &0) (mod &p)
      ==> (x pow p == c2 * x pow 2 + c1 * x + c0) (mod &p))
     ==> prime p
         ==> ~(b rem &p = &0)
             ==> ((x pow 3 + a * x + b == &0) (mod &p)
                 ==> (&0 == c2 * x pow 2 + (c1 - &1) * x + c0) (mod &p))`,
    DISCH_THEN(fun th -> REPEAT DISCH_TAC THEN MP_TAC th) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(INTEGER_RULE
     `(xp == x) (mod p)
      ==> (xp:int == c2 * x pow 2 + c1 * x + c0) (mod p)
           ==> (&0 == c2 * x pow 2 + (c1 - &1) * x + c0) (mod p)`) THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP (INTEGER_RULE
     `(x pow 3 + a * x + b:int == &0) (mod p)
      ==> coprime(b,p) ==> coprime(x,p)`)) THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC(INTEGER_RULE
       `(b rem p == b) (mod p) /\ coprime(b rem p,p) ==> coprime(b,p)`) THEN
      REWRITE_TAC[INT_REM_MOD_SELF] THEN UNDISCH_TAC `~(b rem &p = &0)` THEN
      SUBGOAL_THEN `&0 <= b rem &p /\ b rem &p < &p` MP_TAC THENL
       [ASM_REWRITE_TAC[INT_REM_POS_EQ; INT_LT_REM_EQ] THEN
        ASM_SIMP_TAC[INT_OF_NUM_EQ; PRIME_IMP_NZ; INT_OF_NUM_LT; LE_1];
        SPEC_TAC(`b rem &p`,`x:int`)] THEN
      REWRITE_TAC[GSYM INT_FORALL_POS; IMP_CONJ] THEN
      X_GEN_TAC `n:num` THEN REWRITE_TAC[INT_OF_NUM_EQ; INT_OF_NUM_LT] THEN
      REPEAT DISCH_TAC THEN REWRITE_TAC[GSYM num_coprime] THEN
      ONCE_REWRITE_TAC[COPRIME_SYM] THEN ASM_SIMP_TAC[PRIME_COPRIME_EQ] THEN
      DISCH_THEN(MP_TAC o MATCH_MP DIVIDES_LE) THEN ASM_ARITH_TAC;
      DISCH_THEN(MP_TAC o MATCH_MP (INTEGER_RULE
       `coprime(b,p) ==> (b rem p == b) (mod p) ==> coprime(b rem p,p)`)) THEN
      REWRITE_TAC[INT_REM_MOD_SELF]] THEN
    REWRITE_TAC[GSYM INT_REM_EQ] THEN ONCE_REWRITE_TAC[GSYM INT_POW_REM] THEN
    SUBGOAL_THEN `&0 <= x rem &p /\ x rem &p < &p` MP_TAC THENL
     [ASM_REWRITE_TAC[INT_REM_POS_EQ; INT_LT_REM_EQ] THEN
      ASM_SIMP_TAC[INT_OF_NUM_EQ; PRIME_IMP_NZ; INT_OF_NUM_LT; LE_1];
      SPEC_TAC(`x rem &p`,`x:int`)] THEN
    REWRITE_TAC[GSYM INT_FORALL_POS; IMP_CONJ] THEN
    REWRITE_TAC[INT_POW_REM; GSYM num_coprime; INT_OF_NUM_LT] THEN
    X_GEN_TAC `n:num` THEN REPEAT STRIP_TAC THEN
    REWRITE_TAC[INT_OF_NUM_POW; INT_OF_NUM_REM; INT_OF_NUM_EQ] THEN
    MP_TAC(SPECL [`n:num`; `p:num`] FERMAT_LITTLE_PRIME) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o MATCH_MP (NUMBER_RULE
     `(x EXP a == 1) (mod p) ==> (x * x EXP a == x) (mod p)`)) THEN
    ASM_SIMP_TAC[GSYM(CONJUNCT2 EXP); CONG; MOD_LT] THEN
    ASM_SIMP_TAC[PRIME_IMP_NZ; ARITH_RULE `~(p = 0) ==> SUC(p - 1) = p`])
  and lemma_tolin = prove
   (`(x pow 3 + a * x + b == &0) (mod p) /\
     (&0 == &1 * x pow 2 + c1 * x + c0) (mod p)
     ==> (&0:int == &0 * x pow 2 +
                    (a + c1 pow 2 - c0) * x + (b + c0 * c1)) (mod p)`,
    INTEGER_TAC)
  and lemma_toconst = prove
   (`(&0:int == &1 * x pow 2 + c1 * x + c0) (mod p) /\
     (&0:int == &0 * x pow 2 + &1 * x + d) (mod p)
     ==> (&0:int == c0 - d * (c1 - d)) (mod p)`,
    INTEGER_TAC)
  and lemma_3_2 = prove
   (`(x pow 3 + a * x + b:int == &0) (mod p)
     ==> (y == c3 * x pow 3 + c2 * x pow 2 + c1 * x + c0) (mod p)
         ==> (y == c2 * x pow 2 + (c1 - a * c3) * x + (c0 - b * c3)) (mod p)`,
    INTEGER_TAC)
  and lemma_4_3 = prove
   (`(x pow 3 + a * x + b:int == &0) (mod p)
     ==> (y == c4 * x pow 4 + c3 * x pow 3 + c2 * x pow 2 + c1 * x + c0) (mod p)
         ==> (y == c3 * x pow 3 + (c2 - a * c4) * x pow 2 +
                   (c1 - b * c4) * x + c0) (mod p)`,
    INTEGER_TAC)
  and lemma_rem = prove
   (`(y:int == c2 * x pow 2 + c1 * x + c0) (mod p)
     ==> (y == c2 rem p * x pow 2 + c1 rem p * x + c0 rem p) (mod p)`,
    MATCH_MP_TAC(INTEGER_RULE
     `(c2:int == c2') (mod p) /\ (c1 == c1') (mod p) /\ (c0 == c0') (mod p)
      ==> (y:int == c2 * x pow 2 + c1 * x + c0) (mod p)
          ==> (y:int == c2' * x pow 2 + c1' * x + c0') (mod p)`) THEN
    REWRITE_TAC[INT_CONG_RREM] THEN CONV_TAC INTEGER_RULE)
  and lemma_mulx = prove
   (`((x:int) pow n == c2 * x pow 2 + c1 * x + c0) (mod p)
     ==> (x pow (n + 1) == c2 * x pow 3 + c1 * x pow 2 + c0 * x + &0) (mod p)`,
    REWRITE_TAC[INT_POW_ADD] THEN INTEGER_TAC)
  and lemma_sqr = prove
   (`((x:int) pow n == c2 * x pow 2 + c1 * x + c0) (mod p)
     ==> (x pow (2 * n) ==
          (c2 pow 2) * x pow 4 + (&2 * c1 * c2) * x pow 3 +
          (c1 pow 2 + &2 * c0 * c2) * x pow 2 +
          (&2 * c0 * c1) * x +
          c0 pow 2) (mod p)`,
    REWRITE_TAC[MULT_2; INT_POW_ADD] THEN
    INTEGER_TAC)
  and lemma_mulc = prove
   (`(y:int == c2 * x pow 2 + c1 * x + c0) (mod p)
     ==> !c. (c * y == (c * c2) * x pow 2 + (c * c1) * x + c * c0) (mod p)`,
    INTEGER_TAC)
  and pth0 = INTEGER_RULE `!p. ((x:int) pow 0 == &0 * x pow 2 + &0 * x + &1)
                               (mod &p)` in
  fun tm primeth ->
    let th = ASSUME tm in
    let rule_3_2 = MATCH_MP(MATCH_MP lemma_3_2 th)
    and rule_4_3 = MATCH_MP(MATCH_MP lemma_4_3 th)
    and rule_mulx = MATCH_MP lemma_mulx
    and rule_mulc = MATCH_MP lemma_mulc
    and rule_sqr = MATCH_MP lemma_sqr
    and rule_rem = MATCH_MP lemma_rem in
    let qtm = rand(concl primeth) in
    let q = dest_numeral qtm in
    let th0 = SPEC qtm pth0 in
    let rec power_rule n =
      if n =/ num_0 then th0 else
      let m = quo_num n num_2 in
      let th1 = power_rule m in
      let th2 = (CONV_RULE INT_REDUCE_CONV o
                 CONV_RULE NUM_REDUCE_CONV o
                 rule_rem o rule_3_2 o rule_4_3 o rule_sqr) th1 in
      if mod_num n num_2 =/ num_0 then th2 else
      (CONV_RULE INT_REDUCE_CONV o
       CONV_RULE NUM_REDUCE_CONV o
       rule_rem o rule_3_2 o rule_mulx) th2 in
    let th1 = DISCH tm (power_rule q) in
    let th2 = MP (MATCH_MP lemma_flt th1) primeth in
    let th3 = MP th2 (EQT_ELIM(INT_REDUCE_CONV(lhand(concl th2)))) in
    let th4 = (CONV_RULE INT_REDUCE_CONV o rule_rem) (UNDISCH th3) in
    let hc = dest_intconst(lhand(lhand(rand(rator(concl th4))))) in
    let th5 = SPEC (mk_intconst(num_modinv q hc)) (rule_mulc th4) in
    let th6 = (CONV_RULE INT_REDUCE_CONV o rule_rem) th5 in
    let th7 = MATCH_MP lemma_tolin (CONJ (ASSUME tm) th6) in
    let th8 = (CONV_RULE INT_REDUCE_CONV o rule_rem) th7 in
    let hc = dest_intconst(lhand(lhand(rand(rand(rator(concl th8)))))) in
    let th9 = SPEC (mk_intconst(num_modinv q hc)) (rule_mulc th8) in
    let tha = (CONV_RULE INT_REDUCE_CONV o rule_rem) th9 in
    let thb = MATCH_MP lemma_toconst (CONJ th6 tha) in
    let thc = CONV_RULE INT_REDUCE_CONV (REWRITE_RULE[GSYM INT_REM_EQ] thb) in
    NOT_INTRO(DISCH tm thc);;

let NIST_EXCLUDE_ROOTS_TAC(primeth,pth,bth) =
  X_GEN_TAC `x:int` THEN REWRITE_TAC[INT_ARITH
   `x pow 3 - &3 * x + b:int = x pow 3 + (-- &3) * x + b`] THEN
  REWRITE_TAC[pth; bth] THEN
  W(fun (asl,w) -> ACCEPT_TAC
    (EXCLUDE_ELLIPTIC_CURVE_ROOTS (rand w) (REWRITE_RULE[pth] primeth)));;

let NO_ROOTS_P192 = prove
 (`!x:int. ~((x pow 3 - &3 * x + &b_192 == &0) (mod &p_192))`,
  NIST_EXCLUDE_ROOTS_TAC(PRIME_P192,p_192,b_192));;

let NO_ROOTS_P224 = prove
 (`!x:int. ~((x pow 3 - &3 * x + &b_224 == &0) (mod &p_224))`,
  NIST_EXCLUDE_ROOTS_TAC(PRIME_P224,p_224,b_224));;

let NO_ROOTS_P256 = prove
 (`!x:int. ~((x pow 3 - &3 * x + &b_256 == &0) (mod &p_256))`,
  NIST_EXCLUDE_ROOTS_TAC(PRIME_P256,p_256,b_256));;

let NO_ROOTS_P384 = prove
 (`!x:int. ~((x pow 3 - &3 * x + &b_384 == &0) (mod &p_384))`,
  NIST_EXCLUDE_ROOTS_TAC(PRIME_P384,p_384,b_384));;

let NO_ROOTS_P521 = prove
 (`!x:int. ~((x pow 3 - &3 * x + &b_521 == &0) (mod &p_521))`,
  NIST_EXCLUDE_ROOTS_TAC(PRIME_P521,p_521,b_521));;

(* ------------------------------------------------------------------------- *)
(* HOL conversions for explicit calculation with group operations.           *)
(* ------------------------------------------------------------------------- *)

let INTEGER_MOD_RING_INV_CONV =
  let pth = prove
   (`!p x y.
        &0 <= x /\ x < &p /\ &0 <= y /\ y < &p /\ (x * y) rem &p = &1 rem &p
        ==> ring_inv (integer_mod_ring p) x = y`,
    REPEAT GEN_TAC THEN ASM_CASES_TAC `&0:int < &p` THENL
     [RULE_ASSUM_TAC(REWRITE_RULE[INT_OF_NUM_LT]); ASM_INT_ARITH_TAC] THEN
    STRIP_TAC THEN MATCH_MP_TAC RING_RINV_UNIQUE THEN
    ASM_SIMP_TAC[INTEGER_MOD_RING; IN_ELIM_THM]) in
  fun tm ->
    match tm with
      Comb(Comb(Const("ring_inv",_),
                Comb(Const("integer_mod_ring",_),qtm)),xtm) ->
        let q = dest_numeral qtm and x = dest_intconst xtm in
        let y = num_modinv q x in
        let th0 = SPECL [qtm; xtm; mk_intconst y] pth in
        MP th0 (EQT_ELIM(INT_REDUCE_CONV(lhand(concl th0))))
  | _ -> failwith "INTEGER_MOD_RING_INV_CONV";;

let NIST_CARRIER_CONV =
  let pth = GENL [`f:A ring`; `a:A`; `b:A`]
        (PURE_ONCE_REWRITE_RULE
          [SET_RULE `weierstrass_curve q x <=> x IN weierstrass_curve q`]
          weierstrass_curve) in
  let ths = map
   (fun gth ->
        let hth = ISPECL (striplist dest_pair (rand(rand(concl gth)))) pth in
        let ith = PURE_ONCE_REWRITE_RULE[GSYM gth] hth in
        CONJ (CONJUNCT1 ith)
         (SIMP_RULE
           [INTEGER_MOD_RING; ARITH; IN_ELIM_THM; INTEGER_MOD_RING_POW]
           (CONJUNCT2 ith)))
   [REWRITE_RULE[b_192; p_192] (CONJUNCT1 P192_GROUP);
    REWRITE_RULE[b_224; p_224] (CONJUNCT1 P224_GROUP);
    REWRITE_RULE[b_256; p_256] (CONJUNCT1 P256_GROUP);
    REWRITE_RULE[b_384; p_384] (CONJUNCT1 P384_GROUP);
    REWRITE_RULE[b_521; p_521] (CONJUNCT1 P521_GROUP)] in
  GEN_REWRITE_CONV I ths THENC INT_REDUCE_CONV;;

let NIST_ID_CONV =
  GEN_REWRITE_CONV I
   (map (CONJUNCT1 o CONJUNCT2)
        [P192_GROUP; P224_GROUP; P256_GROUP; P384_GROUP; P521_GROUP]);;

let NIST_INV_CONV =
  let ths = map
   (fun gth ->
        let hth = PART_MATCH (rator o lhand o lhand) weierstrass_neg
                             (rand(concl gth)) in
        let ith = ONCE_REWRITE_RULE[GSYM gth] hth in
        REWRITE_RULE[INTEGER_MOD_RING] ith)
   [REWRITE_RULE[b_192; p_192] (el 2 (CONJUNCTS P192_GROUP));
    REWRITE_RULE[b_224; p_224] (el 2 (CONJUNCTS P224_GROUP));
    REWRITE_RULE[b_256; p_256] (el 2 (CONJUNCTS P256_GROUP));
    REWRITE_RULE[b_384; p_384] (el 2 (CONJUNCTS P384_GROUP));
    REWRITE_RULE[b_521; p_521] (el 2 (CONJUNCTS P521_GROUP))] in
  GEN_REWRITE_CONV I ths THENC INT_REDUCE_CONV;;

let NIST_MUL_CONV =
  let pth = GENL [`f:A ring`; `a:A`; `b:A`] weierstrass_add in
  let ths = map
   (fun gth ->
        let hth = ISPECL (striplist dest_pair (rand(rand(concl gth)))) pth in
        let ith = ONCE_REWRITE_RULE[GSYM gth] hth in
        REWRITE_RULE[INTEGER_MOD_RING; ring_div; INTEGER_MOD_RING_POW;
          LET_DEF; LET_END_DEF; ring_sub; INTEGER_MOD_RING_OF_NUM] ith)
   [REWRITE_RULE[b_192; p_192] (el 3 (CONJUNCTS P192_GROUP));
    REWRITE_RULE[b_224; p_224] (el 3 (CONJUNCTS P224_GROUP));
    REWRITE_RULE[b_256; p_256] (el 3 (CONJUNCTS P256_GROUP));
    REWRITE_RULE[b_384; p_384] (el 3 (CONJUNCTS P384_GROUP));
    REWRITE_RULE[b_521; p_521] (el 3 (CONJUNCTS P521_GROUP))] in
  GEN_REWRITE_CONV I ths THENC
  DEPTH_CONV(INT_RED_CONV ORELSEC INTEGER_MOD_RING_INV_CONV);;

let NIST_POW_CONV =
  let pth = prove
   (`!G x m n.
        x IN group_carrier G
        ==> group_pow G x (2 * n) = group_pow G (group_mul G x x) n`,
   SIMP_TAC[GSYM GROUP_POW_2; GROUP_POW_POW])
  and dth = prove
   (`NUMERAL(BIT0 n) = 2 * NUMERAL n`,
    REWRITE_TAC[MULT_2] THEN REWRITE_TAC[BIT0] THEN
    REWRITE_TAC[NUMERAL]) in
  let num_half_CONV = GEN_REWRITE_CONV I [dth] in
  let conv_0 =
    GEN_REWRITE_CONV I [CONJUNCT1 group_pow] THENC
    NIST_ID_CONV
  and conv_1 = GEN_REWRITE_CONV I [CONJUNCT2 group_pow]
  and conv_2 = PART_MATCH (lhand o rand) pth in
  let rec conv tm =
    match tm with
      Comb(Comb(Comb(Const("group_pow",_),g),x),ntm) ->
        let n = dest_numeral ntm in
        if n =/ num_0 then conv_0 tm
        else if mod_num n num_2 =/ num_1 then
          (RAND_CONV num_CONV THENC conv_1 THENC
           RAND_CONV conv THENC NIST_MUL_CONV) tm
        else
          let th1 = RAND_CONV num_half_CONV tm in
          let th2 = conv_2 (rand(concl th1)) in
          let th3 = MP th2
           (EQT_ELIM((NIST_CARRIER_CONV(lhand(concl th2))))) in
          let th4 = TRANS th1 th3 in
          CONV_RULE(RAND_CONV(LAND_CONV NIST_MUL_CONV THENC conv)) th4
     | _ -> failwith "wozz" in
  conv;;

(* ------------------------------------------------------------------------- *)
(* Proof that the NIST curve groups p_xxx have the sizes n_xxx claimed.      *)
(* Since the orders n_xxx are all prime, we just need to exhibit a           *)
(* generator with g^n = 1 (n g = 0 in additive terminology) and then do      *)
(* a little bit more work rule out small multiples of n as the order.        *)
(* For multiples >= 3 this follows from the trivial bound; for 2 n we        *)
(* use a kind of dollar-store Sylow theorem to show the order isn't          *)
(* even, since that would imply the existence of an element of order 2,      *)
(* while directly above we have proved that there are no such points.        *)
(* It would be more direct and natural to use the Hasse bound, implying      *)
(* the order is close to p, but we'd have to prove that result formally.     *)
(* ------------------------------------------------------------------------- *)

let CAUCHY_GROUP_THEOREM_2 = prove
 (`!G:A group.
        FINITE(group_carrier G) /\ EVEN(CARD(group_carrier G))
        ==> ?x. x IN group_carrier G /\ group_element_order G x = 2`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CAUCHY_GROUP_THEOREM THEN
  ASM_REWRITE_TAC[PRIME_2; DIVIDES_2]);;

let GROUP_ADHOC_ORDER_UNIQUE_LEMMA = prove
 (`!G (a:A) p.
      FINITE(group_carrier G) /\ CARD(group_carrier G) < 3 * p /\
      (!x. x IN group_carrier G /\ group_inv G x = x ==> x = group_id G) /\
      a IN group_carrier G /\ group_element_order G a = p
      ==> (group_carrier G) HAS_SIZE p`,
  SIMP_TAC[HAS_SIZE] THEN REPEAT STRIP_TAC THEN MP_TAC
   (SPECL [`G:A group`; `a:A`] GROUP_ELEMENT_ORDER_DIVIDES_GROUP_ORDER) THEN
  ASM_REWRITE_TAC[divides; LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC `d:num` THEN
  ASM_CASES_TAC `d = 0` THEN
  ASM_SIMP_TAC[CARD_EQ_0; MULT_CLAUSES; GROUP_CARRIER_NONEMPTY] THEN
  ASM_CASES_TAC `d = 1` THEN ASM_REWRITE_TAC[MULT_CLAUSES] THEN
  ASM_CASES_TAC `d = 2` THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THENL
   [MP_TAC(ISPEC `G:A group` CAUCHY_GROUP_THEOREM_2) THEN
    ASM_REWRITE_TAC[EVEN_MULT; ARITH; LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `x:A` THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    ASM_SIMP_TAC[GROUP_ELEMENT_ORDER_EQ_2_ALT] THEN ASM_MESON_TAC[];
    UNDISCH_TAC `CARD(group_carrier(G:A group)) < 3 * p` THEN
    MATCH_MP_TAC(TAUT `~p ==> p ==> q`) THEN ASM_REWRITE_TAC[NOT_LT] THEN
    GEN_REWRITE_TAC RAND_CONV [MULT_SYM] THEN
    ASM_REWRITE_TAC[LE_MULT_RCANCEL] THEN ASM_ARITH_TAC]);;

let GENERATOR_IN_GROUP_CARRIER_192 = prove
 (`G_192 IN group_carrier p192_group`,
  REWRITE_TAC[G_192] THEN CONV_TAC NIST_CARRIER_CONV);;

let GROUP_ELEMENT_ORDER_G192 = prove
 (`group_element_order p192_group G_192 = n_192`,
  SIMP_TAC[GROUP_ELEMENT_ORDER_UNIQUE_PRIME; GENERATOR_IN_GROUP_CARRIER_192;
           PRIME_N192] THEN
  REWRITE_TAC[G_192; el 1 (CONJUNCTS P192_GROUP); option_DISTINCT] THEN
  REWRITE_TAC[n_192] THEN CONV_TAC(LAND_CONV NIST_POW_CONV) THEN
  REFL_TAC);;

let FINITE_GROUP_CARRIER_192 = prove
 (`FINITE(group_carrier p192_group)`,
  REWRITE_TAC[P192_GROUP] THEN MATCH_MP_TAC FINITE_WEIERSTRASS_CURVE THEN
  REWRITE_TAC[FINITE_INTEGER_MOD_RING; FIELD_INTEGER_MOD_RING; PRIME_P192] THEN
  REWRITE_TAC[p_192] THEN CONV_TAC NUM_REDUCE_CONV);;

let SIZE_P192_GROUP = prove
 (`group_carrier p192_group HAS_SIZE n_192`,
  MATCH_MP_TAC GROUP_ADHOC_ORDER_UNIQUE_LEMMA THEN
  EXISTS_TAC `G_192:(int#int)option` THEN
  REWRITE_TAC[GENERATOR_IN_GROUP_CARRIER_192; GROUP_ELEMENT_ORDER_G192;
              FINITE_GROUP_CARRIER_192] THEN
  REWRITE_TAC[P192_GROUP] THEN CONJ_TAC THENL
   [W(MP_TAC o PART_MATCH (lhand o rand)
      CARD_BOUND_WEIERSTRASS_CURVE o lhand o snd) THEN
    REWRITE_TAC[FINITE_INTEGER_MOD_RING; FIELD_INTEGER_MOD_RING] THEN
    REWRITE_TAC[PRIME_P192] THEN ANTS_TAC THENL
     [REWRITE_TAC[p_192] THEN CONV_TAC NUM_REDUCE_CONV;
      MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] LET_TRANS)] THEN
    SIMP_TAC[CARD_INTEGER_MOD_RING; p_192; ARITH] THEN
    REWRITE_TAC[n_192] THEN CONV_TAC NUM_REDUCE_CONV;
    REWRITE_TAC[FORALL_OPTION_THM; IN; FORALL_PAIR_THM] THEN
    REWRITE_TAC[weierstrass_curve; weierstrass_neg; option_DISTINCT] THEN
    MAP_EVERY X_GEN_TAC [`x:int`; `y:int`] THEN REWRITE_TAC[option_INJ] THEN
    SIMP_TAC[INTEGER_MOD_RING; INTEGER_MOD_RING_POW;
             p_192; ARITH; PAIR_EQ; IN_ELIM_THM]] THEN
  ASM_CASES_TAC `y:int = &0` THENL
   [ASM_REWRITE_TAC[] THEN CONV_TAC INT_REDUCE_CONV THEN
    DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC (MP_TAC o SYM)) THEN
    CONV_TAC INT_REM_DOWN_CONV THEN MP_TAC(SPEC `x:int` NO_ROOTS_P192) THEN
    REWRITE_TAC[INT_ARITH `y - &3 * x + b:int = y + (-- &3) * x + b`] THEN
    REWRITE_TAC[GSYM INT_REM_EQ; p_192; INT_REM_ZERO];
    STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o MATCH_MP (INT_ARITH
     `--y rem p = y ==> y rem p = y ==> (--y rem p = y rem p)`)) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[INT_REM_LT]; ALL_TAC] THEN
    REWRITE_TAC[INT_REM_EQ; INTEGER_RULE
     `(--y:int == y) (mod p) <=> p divides (&2 * y)`] THEN
    DISCH_THEN(MP_TAC o MATCH_MP (INTEGER_RULE
     `p divides (a * b:int) ==> coprime(a,p) ==> p divides b`)) THEN
    REWRITE_TAC[GSYM num_coprime; ARITH; COPRIME_2] THEN
    DISCH_THEN(MP_TAC o MATCH_MP INT_DIVIDES_LE) THEN ASM_INT_ARITH_TAC]);;

let GENERATED_P192_GROUP = prove
 (`subgroup_generated p192_group {G_192} = p192_group`,
  SIMP_TAC[SUBGROUP_GENERATED_ELEMENT_ORDER;
           GENERATOR_IN_GROUP_CARRIER_192;
           FINITE_GROUP_CARRIER_192] THEN
  REWRITE_TAC[GROUP_ELEMENT_ORDER_G192;
              REWRITE_RULE[HAS_SIZE] SIZE_P192_GROUP]);;

let GENERATOR_IN_GROUP_CARRIER_224 = prove
 (`G_224 IN group_carrier p224_group`,
  REWRITE_TAC[G_224] THEN CONV_TAC NIST_CARRIER_CONV);;

let GROUP_ELEMENT_ORDER_G224 = prove
 (`group_element_order p224_group G_224 = n_224`,
  SIMP_TAC[GROUP_ELEMENT_ORDER_UNIQUE_PRIME; GENERATOR_IN_GROUP_CARRIER_224;
           PRIME_N224] THEN
  REWRITE_TAC[G_224; el 1 (CONJUNCTS P224_GROUP); option_DISTINCT] THEN
  REWRITE_TAC[n_224] THEN CONV_TAC(LAND_CONV NIST_POW_CONV) THEN
  REFL_TAC);;

let FINITE_GROUP_CARRIER_224 = prove
 (`FINITE(group_carrier p224_group)`,
  REWRITE_TAC[P224_GROUP] THEN MATCH_MP_TAC FINITE_WEIERSTRASS_CURVE THEN
  REWRITE_TAC[FINITE_INTEGER_MOD_RING; FIELD_INTEGER_MOD_RING; PRIME_P224] THEN
  REWRITE_TAC[p_224] THEN CONV_TAC NUM_REDUCE_CONV);;

let SIZE_P224_GROUP = prove
 (`group_carrier p224_group HAS_SIZE n_224`,
  MATCH_MP_TAC GROUP_ADHOC_ORDER_UNIQUE_LEMMA THEN
  EXISTS_TAC `G_224:(int#int)option` THEN
  REWRITE_TAC[GENERATOR_IN_GROUP_CARRIER_224; GROUP_ELEMENT_ORDER_G224;
              FINITE_GROUP_CARRIER_224] THEN
  REWRITE_TAC[P224_GROUP] THEN CONJ_TAC THENL
   [W(MP_TAC o PART_MATCH (lhand o rand)
      CARD_BOUND_WEIERSTRASS_CURVE o lhand o snd) THEN
    REWRITE_TAC[FINITE_INTEGER_MOD_RING; FIELD_INTEGER_MOD_RING] THEN
    REWRITE_TAC[PRIME_P224] THEN ANTS_TAC THENL
     [REWRITE_TAC[p_224] THEN CONV_TAC NUM_REDUCE_CONV;
      MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] LET_TRANS)] THEN
    SIMP_TAC[CARD_INTEGER_MOD_RING; p_224; ARITH] THEN
    REWRITE_TAC[n_224] THEN CONV_TAC NUM_REDUCE_CONV;
    REWRITE_TAC[FORALL_OPTION_THM; IN; FORALL_PAIR_THM] THEN
    REWRITE_TAC[weierstrass_curve; weierstrass_neg; option_DISTINCT] THEN
    MAP_EVERY X_GEN_TAC [`x:int`; `y:int`] THEN REWRITE_TAC[option_INJ] THEN
    SIMP_TAC[INTEGER_MOD_RING; INTEGER_MOD_RING_POW;
             p_224; ARITH; PAIR_EQ; IN_ELIM_THM]] THEN
  ASM_CASES_TAC `y:int = &0` THENL
   [ASM_REWRITE_TAC[] THEN CONV_TAC INT_REDUCE_CONV THEN
    DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC (MP_TAC o SYM)) THEN
    CONV_TAC INT_REM_DOWN_CONV THEN MP_TAC(SPEC `x:int` NO_ROOTS_P224) THEN
    REWRITE_TAC[INT_ARITH `y - &3 * x + b:int = y + (-- &3) * x + b`] THEN
    REWRITE_TAC[GSYM INT_REM_EQ; p_224; INT_REM_ZERO];
    STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o MATCH_MP (INT_ARITH
     `--y rem p = y ==> y rem p = y ==> (--y rem p = y rem p)`)) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[INT_REM_LT]; ALL_TAC] THEN
    REWRITE_TAC[INT_REM_EQ; INTEGER_RULE
     `(--y:int == y) (mod p) <=> p divides (&2 * y)`] THEN
    DISCH_THEN(MP_TAC o MATCH_MP (INTEGER_RULE
     `p divides (a * b:int) ==> coprime(a,p) ==> p divides b`)) THEN
    REWRITE_TAC[GSYM num_coprime; ARITH; COPRIME_2] THEN
    DISCH_THEN(MP_TAC o MATCH_MP INT_DIVIDES_LE) THEN ASM_INT_ARITH_TAC]);;

let GENERATED_P224_GROUP = prove
 (`subgroup_generated p224_group {G_224} = p224_group`,
  SIMP_TAC[SUBGROUP_GENERATED_ELEMENT_ORDER;
           GENERATOR_IN_GROUP_CARRIER_224;
           FINITE_GROUP_CARRIER_224] THEN
  REWRITE_TAC[GROUP_ELEMENT_ORDER_G224;
              REWRITE_RULE[HAS_SIZE] SIZE_P224_GROUP]);;

let GENERATOR_IN_GROUP_CARRIER_256 = prove
 (`G_256 IN group_carrier p256_group`,
  REWRITE_TAC[G_256] THEN CONV_TAC NIST_CARRIER_CONV);;

let GROUP_ELEMENT_ORDER_G256 = prove
 (`group_element_order p256_group G_256 = n_256`,
  SIMP_TAC[GROUP_ELEMENT_ORDER_UNIQUE_PRIME; GENERATOR_IN_GROUP_CARRIER_256;
           PRIME_N256] THEN
  REWRITE_TAC[G_256; el 1 (CONJUNCTS P256_GROUP); option_DISTINCT] THEN
  REWRITE_TAC[n_256] THEN CONV_TAC(LAND_CONV NIST_POW_CONV) THEN
  REFL_TAC);;

let FINITE_GROUP_CARRIER_256 = prove
 (`FINITE(group_carrier p256_group)`,
  REWRITE_TAC[P256_GROUP] THEN MATCH_MP_TAC FINITE_WEIERSTRASS_CURVE THEN
  REWRITE_TAC[FINITE_INTEGER_MOD_RING; FIELD_INTEGER_MOD_RING; PRIME_P256] THEN
  REWRITE_TAC[p_256] THEN CONV_TAC NUM_REDUCE_CONV);;

let SIZE_P256_GROUP = prove
 (`group_carrier p256_group HAS_SIZE n_256`,
  MATCH_MP_TAC GROUP_ADHOC_ORDER_UNIQUE_LEMMA THEN
  EXISTS_TAC `G_256:(int#int)option` THEN
  REWRITE_TAC[GENERATOR_IN_GROUP_CARRIER_256; GROUP_ELEMENT_ORDER_G256;
              FINITE_GROUP_CARRIER_256] THEN
  REWRITE_TAC[P256_GROUP] THEN CONJ_TAC THENL
   [W(MP_TAC o PART_MATCH (lhand o rand)
      CARD_BOUND_WEIERSTRASS_CURVE o lhand o snd) THEN
    REWRITE_TAC[FINITE_INTEGER_MOD_RING; FIELD_INTEGER_MOD_RING] THEN
    REWRITE_TAC[PRIME_P256] THEN ANTS_TAC THENL
     [REWRITE_TAC[p_256] THEN CONV_TAC NUM_REDUCE_CONV;
      MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] LET_TRANS)] THEN
    SIMP_TAC[CARD_INTEGER_MOD_RING; p_256; ARITH] THEN
    REWRITE_TAC[n_256] THEN CONV_TAC NUM_REDUCE_CONV;
    REWRITE_TAC[FORALL_OPTION_THM; IN; FORALL_PAIR_THM] THEN
    REWRITE_TAC[weierstrass_curve; weierstrass_neg; option_DISTINCT] THEN
    MAP_EVERY X_GEN_TAC [`x:int`; `y:int`] THEN REWRITE_TAC[option_INJ] THEN
    SIMP_TAC[INTEGER_MOD_RING; INTEGER_MOD_RING_POW;
             p_256; ARITH; PAIR_EQ; IN_ELIM_THM]] THEN
  ASM_CASES_TAC `y:int = &0` THENL
   [ASM_REWRITE_TAC[] THEN CONV_TAC INT_REDUCE_CONV THEN
    DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC (MP_TAC o SYM)) THEN
    CONV_TAC INT_REM_DOWN_CONV THEN MP_TAC(SPEC `x:int` NO_ROOTS_P256) THEN
    REWRITE_TAC[INT_ARITH `y - &3 * x + b:int = y + (-- &3) * x + b`] THEN
    REWRITE_TAC[GSYM INT_REM_EQ; p_256; INT_REM_ZERO];
    STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o MATCH_MP (INT_ARITH
     `--y rem p = y ==> y rem p = y ==> (--y rem p = y rem p)`)) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[INT_REM_LT]; ALL_TAC] THEN
    REWRITE_TAC[INT_REM_EQ; INTEGER_RULE
     `(--y:int == y) (mod p) <=> p divides (&2 * y)`] THEN
    DISCH_THEN(MP_TAC o MATCH_MP (INTEGER_RULE
     `p divides (a * b:int) ==> coprime(a,p) ==> p divides b`)) THEN
    REWRITE_TAC[GSYM num_coprime; ARITH; COPRIME_2] THEN
    DISCH_THEN(MP_TAC o MATCH_MP INT_DIVIDES_LE) THEN ASM_INT_ARITH_TAC]);;

let GENERATED_P256_GROUP = prove
 (`subgroup_generated p256_group {G_256} = p256_group`,
  SIMP_TAC[SUBGROUP_GENERATED_ELEMENT_ORDER;
           GENERATOR_IN_GROUP_CARRIER_256;
           FINITE_GROUP_CARRIER_256] THEN
  REWRITE_TAC[GROUP_ELEMENT_ORDER_G256;
              REWRITE_RULE[HAS_SIZE] SIZE_P256_GROUP]);;

let GENERATOR_IN_GROUP_CARRIER_384 = prove
 (`G_384 IN group_carrier p384_group`,
  REWRITE_TAC[G_384] THEN CONV_TAC NIST_CARRIER_CONV);;

let GROUP_ELEMENT_ORDER_G384 = prove
 (`group_element_order p384_group G_384 = n_384`,
  SIMP_TAC[GROUP_ELEMENT_ORDER_UNIQUE_PRIME; GENERATOR_IN_GROUP_CARRIER_384;
           PRIME_N384] THEN
  REWRITE_TAC[G_384; el 1 (CONJUNCTS P384_GROUP); option_DISTINCT] THEN
  REWRITE_TAC[n_384] THEN CONV_TAC(LAND_CONV NIST_POW_CONV) THEN
  REFL_TAC);;

let FINITE_GROUP_CARRIER_384 = prove
 (`FINITE(group_carrier p384_group)`,
  REWRITE_TAC[P384_GROUP] THEN MATCH_MP_TAC FINITE_WEIERSTRASS_CURVE THEN
  REWRITE_TAC[FINITE_INTEGER_MOD_RING; FIELD_INTEGER_MOD_RING; PRIME_P384] THEN
  REWRITE_TAC[p_384] THEN CONV_TAC NUM_REDUCE_CONV);;

let SIZE_P384_GROUP = prove
 (`group_carrier p384_group HAS_SIZE n_384`,
  MATCH_MP_TAC GROUP_ADHOC_ORDER_UNIQUE_LEMMA THEN
  EXISTS_TAC `G_384:(int#int)option` THEN
  REWRITE_TAC[GENERATOR_IN_GROUP_CARRIER_384; GROUP_ELEMENT_ORDER_G384;
              FINITE_GROUP_CARRIER_384] THEN
  REWRITE_TAC[P384_GROUP] THEN CONJ_TAC THENL
   [W(MP_TAC o PART_MATCH (lhand o rand)
      CARD_BOUND_WEIERSTRASS_CURVE o lhand o snd) THEN
    REWRITE_TAC[FINITE_INTEGER_MOD_RING; FIELD_INTEGER_MOD_RING] THEN
    REWRITE_TAC[PRIME_P384] THEN ANTS_TAC THENL
     [REWRITE_TAC[p_384] THEN CONV_TAC NUM_REDUCE_CONV;
      MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] LET_TRANS)] THEN
    SIMP_TAC[CARD_INTEGER_MOD_RING; p_384; ARITH] THEN
    REWRITE_TAC[n_384] THEN CONV_TAC NUM_REDUCE_CONV;
    REWRITE_TAC[FORALL_OPTION_THM; IN; FORALL_PAIR_THM] THEN
    REWRITE_TAC[weierstrass_curve; weierstrass_neg; option_DISTINCT] THEN
    MAP_EVERY X_GEN_TAC [`x:int`; `y:int`] THEN REWRITE_TAC[option_INJ] THEN
    SIMP_TAC[INTEGER_MOD_RING; INTEGER_MOD_RING_POW;
             p_384; ARITH; PAIR_EQ; IN_ELIM_THM]] THEN
  ASM_CASES_TAC `y:int = &0` THENL
   [ASM_REWRITE_TAC[] THEN CONV_TAC INT_REDUCE_CONV THEN
    DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC (MP_TAC o SYM)) THEN
    CONV_TAC INT_REM_DOWN_CONV THEN MP_TAC(SPEC `x:int` NO_ROOTS_P384) THEN
    REWRITE_TAC[INT_ARITH `y - &3 * x + b:int = y + (-- &3) * x + b`] THEN
    REWRITE_TAC[GSYM INT_REM_EQ; p_384; INT_REM_ZERO];
    STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o MATCH_MP (INT_ARITH
     `--y rem p = y ==> y rem p = y ==> (--y rem p = y rem p)`)) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[INT_REM_LT]; ALL_TAC] THEN
    REWRITE_TAC[INT_REM_EQ; INTEGER_RULE
     `(--y:int == y) (mod p) <=> p divides (&2 * y)`] THEN
    DISCH_THEN(MP_TAC o MATCH_MP (INTEGER_RULE
     `p divides (a * b:int) ==> coprime(a,p) ==> p divides b`)) THEN
    REWRITE_TAC[GSYM num_coprime; ARITH; COPRIME_2] THEN
    DISCH_THEN(MP_TAC o MATCH_MP INT_DIVIDES_LE) THEN ASM_INT_ARITH_TAC]);;

let GENERATED_P384_GROUP = prove
 (`subgroup_generated p384_group {G_384} = p384_group`,
  SIMP_TAC[SUBGROUP_GENERATED_ELEMENT_ORDER;
           GENERATOR_IN_GROUP_CARRIER_384;
           FINITE_GROUP_CARRIER_384] THEN
  REWRITE_TAC[GROUP_ELEMENT_ORDER_G384;
              REWRITE_RULE[HAS_SIZE] SIZE_P384_GROUP]);;

let GENERATOR_IN_GROUP_CARRIER_521 = prove
 (`G_521 IN group_carrier p521_group`,
  REWRITE_TAC[G_521] THEN CONV_TAC NIST_CARRIER_CONV);;

let GROUP_ELEMENT_ORDER_G521 = prove
 (`group_element_order p521_group G_521 = n_521`,
  SIMP_TAC[GROUP_ELEMENT_ORDER_UNIQUE_PRIME; GENERATOR_IN_GROUP_CARRIER_521;
           PRIME_N521] THEN
  REWRITE_TAC[G_521; el 1 (CONJUNCTS P521_GROUP); option_DISTINCT] THEN
  REWRITE_TAC[n_521] THEN CONV_TAC(LAND_CONV NIST_POW_CONV) THEN
  REFL_TAC);;

let FINITE_GROUP_CARRIER_521 = prove
 (`FINITE(group_carrier p521_group)`,
  REWRITE_TAC[P521_GROUP] THEN MATCH_MP_TAC FINITE_WEIERSTRASS_CURVE THEN
  REWRITE_TAC[FINITE_INTEGER_MOD_RING; FIELD_INTEGER_MOD_RING; PRIME_P521] THEN
  REWRITE_TAC[p_521] THEN CONV_TAC NUM_REDUCE_CONV);;

let SIZE_P521_GROUP = prove
 (`group_carrier p521_group HAS_SIZE n_521`,
  MATCH_MP_TAC GROUP_ADHOC_ORDER_UNIQUE_LEMMA THEN
  EXISTS_TAC `G_521:(int#int)option` THEN
  REWRITE_TAC[GENERATOR_IN_GROUP_CARRIER_521; GROUP_ELEMENT_ORDER_G521;
              FINITE_GROUP_CARRIER_521] THEN
  REWRITE_TAC[P521_GROUP] THEN CONJ_TAC THENL
   [W(MP_TAC o PART_MATCH (lhand o rand)
      CARD_BOUND_WEIERSTRASS_CURVE o lhand o snd) THEN
    REWRITE_TAC[FINITE_INTEGER_MOD_RING; FIELD_INTEGER_MOD_RING] THEN
    REWRITE_TAC[PRIME_P521] THEN ANTS_TAC THENL
     [REWRITE_TAC[p_521] THEN CONV_TAC NUM_REDUCE_CONV;
      MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] LET_TRANS)] THEN
    SIMP_TAC[CARD_INTEGER_MOD_RING; p_521; ARITH] THEN
    REWRITE_TAC[n_521] THEN CONV_TAC NUM_REDUCE_CONV;
    REWRITE_TAC[FORALL_OPTION_THM; IN; FORALL_PAIR_THM] THEN
    REWRITE_TAC[weierstrass_curve; weierstrass_neg; option_DISTINCT] THEN
    MAP_EVERY X_GEN_TAC [`x:int`; `y:int`] THEN REWRITE_TAC[option_INJ] THEN
    SIMP_TAC[INTEGER_MOD_RING; INTEGER_MOD_RING_POW;
             p_521; ARITH; PAIR_EQ; IN_ELIM_THM]] THEN
  ASM_CASES_TAC `y:int = &0` THENL
   [ASM_REWRITE_TAC[] THEN CONV_TAC INT_REDUCE_CONV THEN
    DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC (MP_TAC o SYM)) THEN
    CONV_TAC INT_REM_DOWN_CONV THEN MP_TAC(SPEC `x:int` NO_ROOTS_P521) THEN
    REWRITE_TAC[INT_ARITH `y - &3 * x + b:int = y + (-- &3) * x + b`] THEN
    REWRITE_TAC[GSYM INT_REM_EQ; p_521; INT_REM_ZERO];
    STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o MATCH_MP (INT_ARITH
     `--y rem p = y ==> y rem p = y ==> (--y rem p = y rem p)`)) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[INT_REM_LT]; ALL_TAC] THEN
    REWRITE_TAC[INT_REM_EQ; INTEGER_RULE
     `(--y:int == y) (mod p) <=> p divides (&2 * y)`] THEN
    DISCH_THEN(MP_TAC o MATCH_MP (INTEGER_RULE
     `p divides (a * b:int) ==> coprime(a,p) ==> p divides b`)) THEN
    REWRITE_TAC[GSYM num_coprime; ARITH; COPRIME_2] THEN
    DISCH_THEN(MP_TAC o MATCH_MP INT_DIVIDES_LE) THEN ASM_INT_ARITH_TAC]);;

let GENERATED_P521_GROUP = prove
 (`subgroup_generated p521_group {G_521} = p521_group`,
  SIMP_TAC[SUBGROUP_GENERATED_ELEMENT_ORDER;
           GENERATOR_IN_GROUP_CARRIER_521;
           FINITE_GROUP_CARRIER_521] THEN
  REWRITE_TAC[GROUP_ELEMENT_ORDER_G521;
              REWRITE_RULE[HAS_SIZE] SIZE_P521_GROUP]);;

(* ------------------------------------------------------------------------- *)
(* Point doubling in projective coordinates.                                 *)
(*                                                                           *)
(* Source: Bernstein-Lange [2007] "Faster addition and doubling..."          *)
(* ------------------------------------------------------------------------- *)

(***
 *** http://hyperelliptic.org/EFD/g1p/auto-code/shortw/projective/doubling/dbl-2007-bl.op3
 ***)

let pr_dbl_2007_bl = new_definition
 `pr_dbl_2007_bl (f:A ring,a:A,b:A) (x1,y1,z1) =
      let xx = ring_pow f x1 2 in
      let zz = ring_pow f z1 2 in
      let t0 = ring_mul f (ring_of_num f 3) xx in
      let t1 = ring_mul f a zz in
      let w = ring_add f t1 t0 in
      let t2 = ring_mul f y1 z1 in
      let s = ring_mul f (ring_of_num f 2) t2 in
      let ss = ring_pow f s 2 in
      let sss = ring_mul f s ss in
      let r = ring_mul f y1 s in
      let rr = ring_pow f r 2 in
      let t3 = ring_add f x1 r in
      let t4 = ring_pow f t3 2 in
      let t5 = ring_sub f t4 xx in
      let b = ring_sub f t5 rr in
      let t6 = ring_pow f w 2 in
      let t7 = ring_mul f (ring_of_num f 2) b in
      let h = ring_sub f t6 t7 in
      let x3 = ring_mul f h s in
      let t8 = ring_sub f b h in
      let t9 = ring_mul f (ring_of_num f 2) rr in
      let t10 = ring_mul f w t8 in
      let y3 = ring_sub f t10 t9 in
      let z3 = sss in
      (x3,y3,z3)`;;

let PR_DBL_2007_BL = prove
 (`!f a b x1 y1 z1:A.
        field f /\
        a IN ring_carrier f /\ b IN ring_carrier f /\
        projective_point f (x1,y1,z1)
        ==> projective_eq f (pr_dbl_2007_bl (f,a,b) (x1,y1,z1))
                          (projective_add (f,a,b) (x1,y1,z1) (x1,y1,z1))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[projective_point] THEN STRIP_TAC THEN
  REWRITE_TAC[pr_dbl_2007_bl; projective_add; projective_eq;
              projective_neg; projective_0] THEN
  ASM_CASES_TAC `z1:A = ring_0 f` THEN
  ASM_REWRITE_TAC[projective_add; projective_eq;
                  projective_neg; projective_0] THEN
  ASM_REWRITE_TAC[LET_DEF; LET_END_DEF; PAIR_EQ; projective_eq] THEN
  weierstrass_field_tac THEN ASM_SIMP_TAC[FIELD_IMP_INTEGRAL_DOMAIN]);;

(* ------------------------------------------------------------------------- *)
(* Point doubling in projective coordinates assuming a = -3.                 *)
(*                                                                           *)
(* Source: Bernstein-Lange [2007] "Faster addition and doubling..."          *)
(* ------------------------------------------------------------------------- *)

(***
 *** http://hyperelliptic.org/EFD/g1p/auto-code/shortw/projective-3/doubling/dbl-2007-bl-2.op3
 ***)

let p3_dbl_2007_bl_2 = new_definition
 `p3_dbl_2007_bl_2 (f:A ring,a:A,b:A) (x1,y1,z1) =
      let t0 = ring_sub f x1 z1 in
      let t1 = ring_add f x1 z1 in
      let t2 = ring_mul f t0 t1 in
      let w = ring_mul f (ring_of_num f 3) t2 in
      let t3 = ring_mul f y1 z1 in
      let s = ring_mul f (ring_of_num f 2) t3 in
      let ss = ring_pow f s 2 in
      let sss = ring_mul f s ss in
      let r = ring_mul f y1 s in
      let rr = ring_pow f r 2 in
      let t4 = ring_mul f x1 r in
      let b = ring_mul f (ring_of_num f 2) t4 in
      let t5 = ring_pow f w 2 in
      let t6 = ring_mul f (ring_of_num f 2) b in
      let h = ring_sub f t5 t6 in
      let x3 = ring_mul f h s in
      let t7 = ring_sub f b h in
      let t8 = ring_mul f (ring_of_num f 2) rr in
      let t9 = ring_mul f w t7 in
      let y3 = ring_sub f t9 t8 in
      let z3 = sss in
      (x3,y3,z3)`;;

let P3_DBL_2007_BL_2 = prove
 (`!f a b x1 y1 z1:A.
        field f /\
        a = ring_of_int f (-- &3) /\ b IN ring_carrier f /\
        projective_point f (x1,y1,z1)
        ==> projective_eq f (p3_dbl_2007_bl_2 (f,a,b) (x1,y1,z1))
                            (projective_add (f,a,b) (x1,y1,z1) (x1,y1,z1))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[projective_point] THEN STRIP_TAC THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  REWRITE_TAC[p3_dbl_2007_bl_2; projective_add; projective_eq;
              projective_neg; projective_0] THEN
  ASM_CASES_TAC `z1:A = ring_0 f` THEN
  ASM_REWRITE_TAC[projective_add; projective_eq;
                  projective_neg; projective_0] THEN
  ASM_REWRITE_TAC[LET_DEF; LET_END_DEF; PAIR_EQ; projective_eq] THEN
  weierstrass_field_tac THEN ASM_SIMP_TAC[FIELD_IMP_INTEGRAL_DOMAIN]);;

(* ------------------------------------------------------------------------- *)
(* Pure point addition in projective coordinates. This sequence never uses   *)
(* the value of "a" so there's no special optimized version for a = -3.      *)
(*                                                                           *)
(* Source Cohen-Miyaji-Ono [1998] "Efficient elliptic curve exponentiation"  *)
(*                                                                           *)
(* Note the correctness is not proved in cases where the points are equal    *)
(* (or projectively equivalent), or either input is 0 (point at infinity).   *)
(* ------------------------------------------------------------------------- *)

(***
 *** http://hyperelliptic.org/EFD/g1p/auto-code/shortw/projective/addition/add-1998-cmo-2.op3
 ***)

let pr_add_1998_cmo_2 = new_definition
 `pr_add_1998_cmo_2 (f:A ring,a:A,b:A) (x1,y1,z1) (x2,y2,z2) =
      let y1z2 = ring_mul f y1 z2 in
      let x1z2 = ring_mul f x1 z2 in
      let z1z2 = ring_mul f z1 z2 in
      let t0 = ring_mul f y2 z1 in
      let u = ring_sub f t0 y1z2 in
      let uu = ring_pow f u 2 in
      let t1 = ring_mul f x2 z1 in
      let v = ring_sub f t1 x1z2 in
      let vv = ring_pow f v 2 in
      let vvv = ring_mul f v vv in
      let r = ring_mul f vv x1z2 in
      let t2 = ring_mul f (ring_of_num f 2) r in
      let t3 = ring_mul f uu z1z2 in
      let t4 = ring_sub f t3 vvv in
      let a = ring_sub f t4 t2 in
      let x3 = ring_mul f v a in
      let t5 = ring_sub f r a in
      let t6 = ring_mul f vvv y1z2 in
      let t7 = ring_mul f u t5 in
      let y3 = ring_sub f t7 t6 in
      let z3 = ring_mul f vvv z1z2 in
      (x3,y3,z3)`;;

let PR_ADD_1998_CMO_2 = prove
 (`!f a b x1 y1 z1 x2 y2 z2:A.
        field f /\ ~(ring_char f = 2) /\
        a IN ring_carrier f /\ b IN ring_carrier f /\
        projective_point f (x1,y1,z1) /\ projective_point f (x2,y2,z2) /\
        ~(z1 = ring_0 f) /\ ~(z2 = ring_0 f) /\
        ~(projective_eq f (x1,y1,z1) (x2,y2,z2))
        ==> projective_eq f (pr_add_1998_cmo_2 (f,a,b) (x1,y1,z1) (x2,y2,z2))
                            (projective_add (f,a,b) (x1,y1,z1) (x2,y2,z2))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[projective_point] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  ASM_SIMP_TAC[GSYM RING_CHAR_DIVIDES_PRIME; PRIME_2] THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC)) THEN
  REPEAT(FIRST_X_ASSUM SUBST_ALL_TAC) THEN
  ASM_REWRITE_TAC[projective_eq; pr_add_1998_cmo_2; projective_add] THEN
  REPEAT(COND_CASES_TAC THEN
   ASM_REWRITE_TAC[projective_add; projective_eq;
                   projective_neg; projective_0; LET_DEF; LET_END_DEF]) THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (free_in `(=):A->A->bool` o concl))) THEN
  weierstrass_field_tac);;

(* ------------------------------------------------------------------------- *)
(* Mixed point addition in projective coordinates. Here "mixed" means        *)
(* assuming z2 = 1, which holds if the second point was directly injected    *)
(* from the Weierstrass coordinates via (x,y) |-> (x,y,1). This never uses   *)
(* the value of "a" so there's no special optimized version for a = -3.      *)
(*                                                                           *)
(* Source Cohen-Miyaji-Ono [1998] "Efficient elliptic curve exponentiation"  *)
(*                                                                           *)
(* Note the correctness is not proved in the case where the points are equal *)
(* or projectively equivalent, nor where the first is the group identity     *)
(* (i.e. the point at infinity, anything with z1 = 0 in projective coords).  *)
(* ------------------------------------------------------------------------- *)

(***
 *** http://hyperelliptic.org/EFD/g1p/auto-code/shortw/projective/addition/madd-1998-cmo.op3
 ***)

let pr_madd_1998_cmo = new_definition
 `pr_madd_1998_cmo (f:A ring,a:A,b:A) (x1,y1,z1) (x2,y2,z2) =
      let t0 = ring_mul f y2 z1 in
      let u = ring_sub f t0 y1 in
      let uu = ring_pow f u 2 in
      let t1 = ring_mul f x2 z1 in
      let v = ring_sub f t1 x1 in
      let vv = ring_pow f v 2 in
      let vvv = ring_mul f v vv in
      let r = ring_mul f vv x1 in
      let t2 = ring_mul f (ring_of_num f 2) r in
      let t3 = ring_mul f uu z1 in
      let t4 = ring_sub f t3 vvv in
      let a = ring_sub f t4 t2 in
      let x3 = ring_mul f v a in
      let t5 = ring_sub f r a in
      let t6 = ring_mul f vvv y1 in
      let t7 = ring_mul f u t5 in
      let y3 = ring_sub f t7 t6 in
      let z3 = ring_mul f vvv z1 in
      (x3,y3,z3)`;;

let PR_MADD_1998_CMO = prove
 (`!f a b x1 y1 z1 x2 y2 z2:A.
        field f /\ ~(ring_char f = 2) /\
        a IN ring_carrier f /\ b IN ring_carrier f /\
        projective_point f (x1,y1,z1) /\ projective_point f (x2,y2,z2) /\
        z2 = ring_1 f /\
        ~(z1 = ring_0 f) /\ ~(projective_eq f (x1,y1,z1) (x2,y2,z2))
        ==> projective_eq f (pr_madd_1998_cmo (f,a,b) (x1,y1,z1) (x2,y2,z2))
                            (projective_add (f,a,b) (x1,y1,z1) (x2,y2,z2))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[projective_point] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  ASM_SIMP_TAC[GSYM RING_CHAR_DIVIDES_PRIME; PRIME_2] THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC)) THEN
  REPEAT(FIRST_X_ASSUM SUBST_ALL_TAC) THEN
  ASM_REWRITE_TAC[projective_eq; pr_madd_1998_cmo; projective_add] THEN
  REPEAT(COND_CASES_TAC THEN
   ASM_REWRITE_TAC[projective_add; projective_eq;
                   projective_neg; projective_0; LET_DEF; LET_END_DEF]) THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (free_in `(=):A->A->bool` o concl))) THEN
  weierstrass_field_tac);;

(* ------------------------------------------------------------------------- *)
(* Point doubling in Jacobian coordinates.                                   *)
(*                                                                           *)
(* Source: Bernstein-Lange [2007] "Faster addition and doubling..."          *)
(* ------------------------------------------------------------------------- *)

(***
 *** http://hyperelliptic.org/EFD/g1p/auto-code/shortw/jacobian/doubling/dbl-2007-bl.op3
 ***)

let ja_dbl_2007_bl = new_definition
 `ja_dbl_2007_bl (f:A ring,a:A,b:A) (x1,y1,z1) =
      let xx = ring_pow f x1 2 in
      let yy = ring_pow f y1 2 in
      let yyyy = ring_pow f yy 2 in
      let zz = ring_pow f z1 2 in
      let t0 = ring_add f x1 yy in
      let t1 = ring_pow f t0 2 in
      let t2 = ring_sub f t1 xx in
      let t3 = ring_sub f t2 yyyy in
      let s = ring_mul f (ring_of_num f 2) t3 in
      let t4 = ring_pow f zz 2 in
      let t5 = ring_mul f a t4 in
      let t6 = ring_mul f (ring_of_num f 3) xx in
      let m = ring_add f t6 t5 in
      let t7 = ring_pow f m 2 in
      let t8 = ring_mul f (ring_of_num f 2) s in
      let t = ring_sub f t7 t8 in
      let x3 = t in
      let t9 = ring_sub f s t in
      let t10 = ring_mul f (ring_of_num f 8) yyyy in
      let t11 = ring_mul f m t9 in
      let y3 = ring_sub f t11 t10 in
      let t12 = ring_add f y1 z1 in
      let t13 = ring_pow f t12 2 in
      let t14 = ring_sub f t13 yy in
      let z3 = ring_sub f t14 zz in
      (x3,y3,z3)`;;

let JA_DBL_2007_BL = prove
 (`!f a b x1 y1 z1:A.
        field f /\
        a IN ring_carrier f /\ b IN ring_carrier f /\
        projective_point f (x1,y1,z1)
        ==> jacobian_eq f (ja_dbl_2007_bl (f,a,b) (x1,y1,z1))
                          (jacobian_add (f,a,b) (x1,y1,z1) (x1,y1,z1))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[projective_point] THEN STRIP_TAC THEN
  REWRITE_TAC[ja_dbl_2007_bl; jacobian_add; jacobian_eq;
              jacobian_neg; jacobian_0] THEN
  ASM_CASES_TAC `z1:A = ring_0 f` THEN
  ASM_REWRITE_TAC[jacobian_add; jacobian_eq;
                  jacobian_neg; jacobian_0] THEN
  ASM_REWRITE_TAC[LET_DEF; LET_END_DEF; PAIR_EQ; jacobian_eq] THEN
  weierstrass_field_tac THEN ASM_SIMP_TAC[FIELD_IMP_INTEGRAL_DOMAIN]);;

let JA_DBL_2007_BL' = prove
 (`!f a b x1 y1 z1:A.
        field f /\
        a IN ring_carrier f /\ b IN ring_carrier f /\
        projective_point f (x1,y1,z1) /\
        (z1 = ring_0 f ==> (x1,y1,z1) = jacobian_0 (f,a,b))
        ==> ja_dbl_2007_bl (f,a,b) (x1,y1,z1) =
            jacobian_add (f,a,b) (x1,y1,z1) (x1,y1,z1)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[projective_point] THEN
  ASM_CASES_TAC `z1:A = ring_0 f` THEN
  ASM_REWRITE_TAC[jacobian_add; jacobian_eq; jacobian_0; PAIR_EQ;
                  jacobian_neg; jacobian_0; ja_dbl_2007_bl] THEN
  STRIP_TAC THEN REPEAT(FIRST_X_ASSUM SUBST_ALL_TAC) THEN
  ASM_REWRITE_TAC[jacobian_add; jacobian_eq;
                  jacobian_neg; jacobian_0] THEN
  ASM_REWRITE_TAC[LET_DEF; LET_END_DEF; PAIR_EQ; jacobian_eq] THEN
  weierstrass_field_tac THEN ASM_SIMP_TAC[FIELD_IMP_INTEGRAL_DOMAIN]);;

(* ------------------------------------------------------------------------- *)
(* Point doubling in Jacobian coordinates assuming a = -3.                   *)
(*                                                                           *)
(* Source: Bernstein [2001] "A software implementation of NIST P-224".       *)
(* ------------------------------------------------------------------------- *)

(***
 *** http://hyperelliptic.org/EFD/g1p/auto-code/shortw/jacobian-3/doubling/dbl-2001-b.op3
 ***)

let j3_dbl_2001_b = new_definition
 `j3_dbl_2001_b (f:A ring,a:A,b:A) (x1,y1,z1) =
      let delta = ring_pow f z1 2 in
      let gamma = ring_pow f y1 2 in
      let beta = ring_mul f x1 gamma in
      let t0 = ring_sub f x1 delta in
      let t1 = ring_add f x1 delta in
      let t2 = ring_mul f t0 t1 in
      let alpha = ring_mul f (ring_of_num f 3) t2 in
      let t3 = ring_pow f alpha 2 in
      let t4 = ring_mul f (ring_of_num f 8) beta in
      let x3 = ring_sub f t3 t4 in
      let t5 = ring_add f y1 z1 in
      let t6 = ring_pow f t5 2 in
      let t7 = ring_sub f t6 gamma in
      let z3 = ring_sub f t7 delta in
      let t8 = ring_mul f (ring_of_num f 4) beta in
      let t9 = ring_sub f t8 x3 in
      let t10 = ring_pow f gamma 2 in
      let t11 = ring_mul f (ring_of_num f 8) t10 in
      let t12 = ring_mul f alpha t9 in
      let y3 = ring_sub f t12 t11 in
      (x3,y3,z3)`;;

let J3_DBL_2001_B = prove
 (`!f a b x1 y1 z1:A.
        field f /\
        a = ring_of_int f (-- &3) /\ b IN ring_carrier f /\
        projective_point f (x1,y1,z1)
        ==> jacobian_eq f (j3_dbl_2001_b (f,a,b) (x1,y1,z1))
                          (jacobian_add (f,a,b) (x1,y1,z1) (x1,y1,z1))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[projective_point] THEN STRIP_TAC THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  REWRITE_TAC[j3_dbl_2001_b; jacobian_add; jacobian_eq;
              jacobian_neg; jacobian_0] THEN
  ASM_CASES_TAC `z1:A = ring_0 f` THEN
  ASM_REWRITE_TAC[jacobian_add; jacobian_eq;
                  jacobian_neg; jacobian_0] THEN
  ASM_REWRITE_TAC[LET_DEF; LET_END_DEF; PAIR_EQ; jacobian_eq] THEN
  weierstrass_field_tac THEN ASM_SIMP_TAC[FIELD_IMP_INTEGRAL_DOMAIN]);;

let J3_DBL_2001_B' = prove
 (`!f a b x1 y1 z1:A.
        field f /\
        a = ring_of_int f (-- &3) /\ b IN ring_carrier f /\
        projective_point f (x1,y1,z1) /\
        (z1 = ring_0 f ==> (x1,y1,z1) = jacobian_0 (f,a,b))
        ==> j3_dbl_2001_b (f,a,b) (x1,y1,z1) =
            jacobian_add (f,a,b) (x1,y1,z1) (x1,y1,z1)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[projective_point] THEN
  ASM_CASES_TAC `z1:A = ring_0 f` THEN
  ASM_REWRITE_TAC[jacobian_add; jacobian_eq; jacobian_0; PAIR_EQ;
                  jacobian_neg; jacobian_0; j3_dbl_2001_b] THEN
  STRIP_TAC THEN REPEAT(FIRST_X_ASSUM SUBST_ALL_TAC) THEN
  ASM_REWRITE_TAC[jacobian_add; jacobian_eq;
                  jacobian_neg; jacobian_0] THEN
  ASM_REWRITE_TAC[LET_DEF; LET_END_DEF; PAIR_EQ; jacobian_eq] THEN
  weierstrass_field_tac THEN ASM_SIMP_TAC[FIELD_IMP_INTEGRAL_DOMAIN]);;

(* ------------------------------------------------------------------------- *)
(* Pure point addition in Jacobian coordinates. This sequence never uses     *)
(* the value of "a" so there's no special optimized version for a = -3.      *)
(*                                                                           *)
(* Source: Bernstein-Lange [2007] "Faster addition and doubling..."          *)
(*                                                                           *)
(* Note the correctness is not proved in cases where the points are equal    *)
(* (or projectively equivalent), or either input is 0 (point at infinity).   *)
(* ------------------------------------------------------------------------- *)

(***
 *** http://hyperelliptic.org/EFD/g1p/auto-code/shortw/jacobian/addition/add-2007-bl.op3
 ***)

let ja_add_2007_bl = new_definition
 `ja_add_2007_bl (f:A ring,a:A,b:A) (x1,y1,z1) (x2,y2,z2) =
      let z1z1 = ring_pow f z1 2 in
      let z2z2 = ring_pow f z2 2 in
      let u1 = ring_mul f x1 z2z2 in
      let u2 = ring_mul f x2 z1z1 in
      let t0 = ring_mul f z2 z2z2 in
      let s1 = ring_mul f y1 t0 in
      let t1 = ring_mul f z1 z1z1 in
      let s2 = ring_mul f y2 t1 in
      let h = ring_sub f u2 u1 in
      let t2 = ring_mul f (ring_of_num f 2) h in
      let i = ring_pow f t2 2 in
      let j = ring_mul f h i in
      let t3 = ring_sub f s2 s1 in
      let r = ring_mul f (ring_of_num f 2) t3 in
      let v = ring_mul f u1 i in
      let t4 = ring_pow f r 2 in
      let t5 = ring_mul f (ring_of_num f 2) v in
      let t6 = ring_sub f t4 j in
      let x3 = ring_sub f t6 t5 in
      let t7 = ring_sub f v x3 in
      let t8 = ring_mul f s1 j in
      let t9 = ring_mul f (ring_of_num f 2) t8 in
      let t10 = ring_mul f r t7 in
      let y3 = ring_sub f t10 t9 in
      let t11 = ring_add f z1 z2 in
      let t12 = ring_pow f t11 2 in
      let t13 = ring_sub f t12 z1z1 in
      let t14 = ring_sub f t13 z2z2 in
      let z3 = ring_mul f t14 h in
      (x3,y3,z3)`;;

let JA_ADD_2007_BL = prove
 (`!f a b x1 y1 z1 x2 y2 z2:A.
        field f /\ ~(ring_char f = 2) /\
        a IN ring_carrier f /\ b IN ring_carrier f /\
        projective_point f (x1,y1,z1) /\ projective_point f (x2,y2,z2) /\
        ~(z1 = ring_0 f) /\ ~(z2 = ring_0 f) /\
        ~(jacobian_eq f (x1,y1,z1) (x2,y2,z2))
        ==> jacobian_eq f (ja_add_2007_bl (f,a,b) (x1,y1,z1) (x2,y2,z2))
                          (jacobian_add (f,a,b) (x1,y1,z1) (x2,y2,z2))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[projective_point] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  ASM_SIMP_TAC[GSYM RING_CHAR_DIVIDES_PRIME; PRIME_2] THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC)) THEN
  REPEAT(FIRST_X_ASSUM SUBST_ALL_TAC) THEN
  ASM_REWRITE_TAC[jacobian_eq; ja_add_2007_bl; jacobian_add] THEN
  REPEAT(COND_CASES_TAC THEN
   ASM_REWRITE_TAC[jacobian_add; jacobian_eq;
                   jacobian_neg; jacobian_0; LET_DEF; LET_END_DEF]) THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (free_in `(=):A->A->bool` o concl))) THEN
  weierstrass_field_tac);;

(* ------------------------------------------------------------------------- *)
(* Mixed point addition in Jacobian coordinates. Here "mixed" means          *)
(* assuming z2 = 1, which holds if the second point was directly injected    *)
(* from the Weierstrass coordinates via (x,y) |-> (x,y,1). This never uses   *)
(* the value of "a" so there's no special optimized version for a = -3.      *)
(*                                                                           *)
(* Source: Bernstein-Lange [2007] "Faster addition and doubling..."          *)
(*                                                                           *)
(* Note the correctness is not proved in the case where the points are equal *)
(* or projectively equivalent, nor where the first is the group identity     *)
(* (i.e. the point at infinity, anything with z1 = 0 in projective coords).  *)
(* ------------------------------------------------------------------------- *)

(***
 *** http://hyperelliptic.org/EFD/g1p/auto-code/shortw/jacobian-3/addition/add-2007-bl.op3
 ***)

let ja_madd_2007_bl = new_definition
 `ja_madd_2007_bl (f:A ring,a:A,b:A) (x1,y1,z1) (x2,y2,z2) =
      let z1z1 = ring_pow f z1 2 in
      let u2 = ring_mul f x2 z1z1 in
      let t0 = ring_mul f z1 z1z1 in
      let s2 = ring_mul f y2 t0 in
      let h = ring_sub f u2 x1 in
      let hh = ring_pow f h 2 in
      let i = ring_mul f (ring_of_num f 4) hh in
      let j = ring_mul f h i in
      let t1 = ring_sub f s2 y1 in
      let r = ring_mul f (ring_of_num f 2) t1 in
      let v = ring_mul f x1 i in
      let t2 = ring_pow f r 2 in
      let t3 = ring_mul f (ring_of_num f 2) v in
      let t4 = ring_sub f t2 j in
      let x3 = ring_sub f t4 t3 in
      let t5 = ring_sub f v x3 in
      let t6 = ring_mul f y1 j in
      let t7 = ring_mul f (ring_of_num f 2) t6 in
      let t8 = ring_mul f r t5 in
      let y3 = ring_sub f t8 t7 in
      let t9 = ring_add f z1 h in
      let t10 = ring_pow f t9 2 in
      let t11 = ring_sub f t10 z1z1 in
      let z3 = ring_sub f t11 hh in
      (x3,y3,z3)`;;

let JA_MADD_2007_BL = prove
 (`!f a b x1 y1 z1 x2 y2 z2:A.
        field f /\ ~(ring_char f = 2) /\
        a IN ring_carrier f /\ b IN ring_carrier f /\
        projective_point f (x1,y1,z1) /\ projective_point f (x2,y2,z2) /\
        z2 = ring_1 f /\
        ~(z1 = ring_0 f) /\ ~(jacobian_eq f (x1,y1,z1) (x2,y2,z2))
        ==> jacobian_eq f (ja_madd_2007_bl (f,a,b) (x1,y1,z1) (x2,y2,z2))
                          (jacobian_add (f,a,b) (x1,y1,z1) (x2,y2,z2))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[projective_point] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  ASM_SIMP_TAC[GSYM RING_CHAR_DIVIDES_PRIME; PRIME_2] THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC)) THEN
  REPEAT(FIRST_X_ASSUM SUBST_ALL_TAC) THEN
  ASM_REWRITE_TAC[jacobian_eq; ja_madd_2007_bl; jacobian_add] THEN
  REPEAT(COND_CASES_TAC THEN
   ASM_REWRITE_TAC[jacobian_add; jacobian_eq;
                   jacobian_neg; jacobian_0; LET_DEF; LET_END_DEF]) THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (free_in `(=):A->A->bool` o concl))) THEN
  weierstrass_field_tac);;
