(* ::Package:: *)

(* ::Subtitle:: *)
(*Groups*)


(* Discrete logarithm group *)
Unprotect[p,q,gen];
p=389;
q=97;
gen=25; (* has order q in Zp *)
Protect[p,q,gen];

(* Iteration of all elements of Gq *)
group=Table[PowerMod[gen,x,p],{x,1,q}];
Assert[PowerMod[gen,q,p]==1];
If[VERBOSE,Print["Elements of Gq: ",group]];
group=Union[group];

(* A 4th primitive root of unity in the exponent field is 22 *)
(* Note that the code does not find this value, I found it and hardcoded it *)
Unprotect[d,\[Omega]];
d=4;
\[Omega]=22;
Protect[d,\[Omega]];

(* Check if w is actually a dth root; also check it is not also a root that is smaller than d *)
Assert[PowerMod[\[Omega],d,q]==1]
Assert[Or@@(#==1&/@Most[PowerMod[\[Omega],Divisors[d],q]])==False]

(* Iteration of roots of unity *)
index=Range[0,d-1];
domain=PowerMod[\[Omega],index,q];
If[VERBOSE,Print["Roots of Unity: ",domain]];
