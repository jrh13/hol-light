let mytheory = ref [
`m + 0 = m`;
`m + (SUC n) = SUC(m + n)`;
`m + n = n + m`;
`m + (n + p) = (m + n) + p`;
`(m + n) + p = m + (n + p)`;
`(m + n = 0) <=> (m = 0) /\ (n = 0)`;
`(m + n = m + p) <=> (n = p)`;
`(m + p = n + p) <=> (m = n)`;
`(m + n = m) <=> (n = 0)`;
`(m + n = n) <=> (m = 0)`;
`SUC m = m + SUC(0)`;
`m * 0 = 0`;
`m * (SUC n) = m + (m * n)`;
`(0 * n = 0) /\ (m * 0 = 0) /\ (1 * n = n) /\ (m * 1 = m) /\ ((SUC m) * n = (m * n) + n) /\ (m * (SUC n) = m + (m * n))`;
`m * n = n * m`;
`m * (n + p) = (m * n) + (m * p)`;
`(m + n) * p = (m * p) + (n * p)`;
`m * (n * p) = (m * n) * p`;
`(m * n = 0) <=> (m = 0) \/ (n = 0)`;
`(m * n = m * p) <=> (m = 0) \/ (n = p)`;
`(m * p = n * p) <=> (m = n) \/ (p = 0)`;
`SUC(SUC(0)) * n = n + n`;
`(m * n = SUC(0)) <=> (m = SUC(0)) /\ (n = SUC(0))`;
`(m EXP n = 0) <=> (m = 0) /\ ~(n = 0)`;
`m EXP (n + p) = (m EXP n) * (m EXP p)`;
`SUC(0) EXP n = SUC(0)`;
`n EXP SUC(0) = n`;
`n EXP SUC(SUC(0)) = n * n`;
`(m * n) EXP p = m EXP p * n EXP p`;
`m EXP (n * p) = (m EXP n) EXP p`;
`(SUC m <= n) <=> (m < n)`;
`(m < SUC n) <=> (m <= n)`;
`(SUC m <= SUC n) <=> (m <= n)`;
`(SUC m < SUC n) <=> (m < n)`;
`0 <= n`;
`0 < SUC n`;
`n <= n`;
`~(n < n)`;
`(m <= n /\ n <= m) <=> (m = n)`;
`~(m < n /\ n < m)`;
`~(m <= n /\ n < m)`;
`~(m < n /\ n <= m)`;
`m <= n /\ n <= p ==> m <= p`;
`m < n /\ n < p ==> m < p`;
`m <= n /\ n < p ==> m < p`;
`m < n /\ n <= p ==> m < p`;
`m <= n \/ n <= m`;
`(m < n) \/ (n < m) \/ (m = n)`;
`m <= n \/ n < m`;
`m < n \/ n <= m`;
`0 < n <=> ~(n = 0)`;
`(m <= n) <=> (m < n) \/ (m = n)`;
`(m < n) <=> (m <= n) /\ ~(m = n)`;
`~(m <= n) <=> (n < m)`;
`~(m < n) <=> n <= m`;
`m < n ==> m <= n`;
`(m = n) ==> m <= n`;
`m <= m + n`;
`n <= m + n`;
`(m < m + n) <=> (0 < n)`;
`(n < m + n) <=> (0 < m)`;
`(m + n) <= (m + p) <=> n <= p`;
`(m + p) <= (n + p) <=> (m <= n)`;
`(m + n) < (m + p) <=> n < p`;
`(m + p) < (n + p) <=> (m < n)`;
`m <= p /\ n <= q ==> m + n <= p + q`;
`m <= p /\ n < q ==> m + n < p + q`;
`m < p /\ n <= q ==> m + n < p + q`;
`m < p /\ n < q ==> m + n < p + q`;
`(0 < m * n) <=> (0 < m) /\ (0 < n)`;
`m <= n /\ p <= q ==> m * p <= n * q`;
`~(m = 0) /\ n < p ==> m * n < m * p`;
`(m * n) <= (m * p) <=> (m = 0) \/ n <= p`;
`(m * p) <= (n * p) <=> (m <= n) \/ (p = 0)`;
`(m * n) < (m * p) <=> ~(m = 0) /\ n < p`;
`(m * p) < (n * p) <=> (m < n) /\ ~(p = 0)`;
`(SUC m = SUC n) <=> (m = n)`;
`m < n /\ p < q ==> m * p < n * q`;
`n <= n * n`;
`(P m n <=> P n m) /\ (m <= n ==> P m n) ==> P m n`;
`(P m m) /\ (P m n <=> P n m) /\ (m < n ==> P m n) ==> P m y`;
`((m < n ==> P m) ==> P n) ==> P n`;
`~(EVEN n) <=> ODD n`;
`~(ODD n) <=> EVEN n`;
`EVEN n \/ ODD n`;
`~(EVEN n /\ ODD n)`;
`EVEN(m + n) <=> (EVEN m <=> EVEN n)`;
`EVEN(m * n) <=> EVEN(m) \/ EVEN(n)`;
`EVEN(m EXP n) <=> EVEN(m) /\ ~(n = 0)`;
`ODD(m + n) <=> ~(ODD m <=> ODD n)`;
`ODD(m * n) <=> ODD(m) /\ ODD(n)`;
`ODD(m EXP n) <=> ODD(m) \/ (n = 0)`;
`EVEN(SUC(SUC(0)) * n)`;
`ODD(SUC(SUC(SUC(0)) * n))`;
`(0 - m = 0) /\ (m - 0 = m)`;
`PRE(SUC m - n) = m - n`;
`SUC m - SUC n = m - n`;
`n - n = 0`;
`(m + n) - n = m`;
`(m + n) - m = n`;
`(m - n = 0) <=> m <= n`;
`m - (m + n) = 0`;
`n - (m + n) = 0`;
`n <= m ==> ((m - n) + n = m)`;
`(m + n) - (m + p) = n - p`;
`(m + p) - (n + p) = m - n`;
`m * (n - p) = m * n - m * p`;
`(m - n) * p = m * p - n * p`;
`!n. SUC n - SUC(0) = n`;
`EVEN(m - n) <=> m <= n \/ (EVEN(m) <=> EVEN(n))`;
`ODD(m - n) <=> n < m /\ ~(ODD m <=> ODD n)`;
`0 < FACT n`;
`1 <= FACT n`;
`m <= n ==> FACT m <= FACT n`;
`0 < x EXP n <=> ~(x = 0) \/ (n = 0)`;
`x EXP m < x EXP n <=> SUC(SUC(0)) <= x /\ m < n \/ (x = 0) /\ ~(m = 0) /\ (n = 0)`;
`x EXP m <= x EXP n <=> if x = 0 then (m = 0) ==> (n = 0) else (x = 1) \/ m <= n`;
`~(p = 0) /\ m <= n ==> m DIV p <= n DIV p`;
`P(PRE n) <=> n = SUC m \/ m = 0 /\ n = 0 ==> P m`
]
