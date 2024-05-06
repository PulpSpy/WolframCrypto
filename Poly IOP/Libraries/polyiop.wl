(* ::Package:: *)

(* ::Subtitle:: *)
(*Group Operations*)


(* Group operations for Gq *)
ModMultGq[aaa___]:=Mod[Times[aaa],p]
ModExpGq[ggg_,aaa_]:=PowerMod[ggg,aaa,p]

(* Group operations for Zq (exponents) *)
ModAddZq[aaa___]:=Mod[Plus[aaa],q]
ModMultZq[aaa___]:=Mod[Times[aaa],q]
ModExpZq[ggg_,aaa_]:=PowerMod[ggg,aaa,q]


(* ::Subtitle:: *)
(*Bilinear Pairings*)


(* Pairing: Zq x Zq \[Rule] Zq *)
pairingTable=Import[NotebookDirectory[]<>"Libraries/pairing_q97_p389","Table"];
ModPairing[aaa_,bbb_]:=pairingTable[[Position[group,aaa][[1,1]],Position[group,bbb][[1,1]]]];


(* ::Subtitle:: *)
(*Polynomials*)


(* We use X as the variable in our polynomials *)
Protect[X];

(* Polynomials *)
PolyInterpolate[domain_,data_,q_]:=Expand[InterpolatingPolynomial[Transpose[{domain,data}],X,Modulus->q],Modulus->q]
PolyInterpolatePoints[points_,q_]:=Expand[InterpolatingPolynomial[points,X,Modulus->q],Modulus->q]
PolyEvaluate[poly_,x_,q_]:=Expand[ReplaceAll[poly,X->x],Modulus->q]
PolyDump[poly_,domain_,q_]:=Table[{domain[[i]],PolyEvaluate[poly,domain[[i]],q]},{i,1,Length[domain]}]
PolyMod[poly_]:=Expand[poly,Modulus->q]

(* Overloaded Function Signatures assuming Global Variables *)
PolyDump[poly_,domain_]:=PolyDump[poly,domain,q];
PolyDump[poly_]:=PolyDump[poly,domain,q];
PolyDumpPretty[poly_]:=MatrixForm[Transpose[PolyDump[poly]]];
PolyEvaluate[poly_,x_]:=PolyEvaluate[poly,x,q]



(* ::Subtitle:: *)
(*Polynomial Commitment Scheme (KZG)*)


(* KZG Polynomial Commitment Scheme (PCS) *)
(* tau is the secret evaluation point, hardcoded to 4 to make code deterministic for debugging *)
\[Tau] = RandomInteger[q];
\[Tau]=4;
waste=Prepend[NestList[Mod[\[Tau]*#,q]&,\[Tau],2*d-2],1];
srs=PowerMod[gen,waste,p];

PolyCommitList[poly_,srs_,p_]:=Mod[Times@@Table[ModExpGq[srs[[i]],poly[[i]]],{i,1,Length[poly]}],p];

PolyCommit[poly_,srs_,p_]:=PolyCommitList[CoefficientList[poly,X,Modulus->q],srs,p];

PolyCommit[poly_]:=PolyCommit[poly,srs,p];

getProofPolys[points_,poly_, q_]:=Module[{vP,rP,qP},
vP=Expand[Product[X-points[[i,1]],{i,1,Length[points]}],Modulus->q];
{qP,rP}=PolynomialQuotientRemainder[poly,vP,X,Modulus->q];
{qP,vP,rP}
];

PolyEvaluateProof[poly_,point_]:=Module[{qP,vP,rP},
{qP,vP,rP}=getProofPolys[{{point,PolyEvaluate[poly,point]}},poly,q];
{PolyCommit[poly],point,PolyEvaluate[poly,point],PolyCommit[qP]}
];

PolyEvaluateVerify[{polyCommit_,x_,y_,quCommit_}]:=Module[{lhs,rhs1,rhs2},
lhs=ModPairing[polyCommit,gen];
rhs1=ModPairing[quCommit,PolyCommit[X-x]];
rhs2=ModPairing[PolyCommit[y],gen];
lhs==ModMultGq[rhs1,rhs2]
];
