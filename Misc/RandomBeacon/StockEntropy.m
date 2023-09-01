(* ::Package:: *)

(* ::Section:: *)
(*Library for Estimating Entropy in a Stock*)


(* Stock constructor *)
Stock[S0_,\[Mu]_,\[Sigma]_]:={S0,\[Mu],\[Sigma]};


(* Helper function *)
Slide[f_,l_,w_]:=ListConvolve[ConstantArray[1,w],l,{-1,1},{},Times,f];


(* Estimate drift and diffusion from list of daily closes *)
StockEst[hist_]:=Module[
		{loghist,\[Sigma]imp,\[Mu]imp},

	loghist=Slide[(Log[#2/#1])&,hist,2];
	\[Sigma]imp=StandardDeviation[loghist];
	\[Mu]imp=Mean[loghist]+(1/2)*(\[Sigma]imp)^2;

	Stock[Last[hist],\[Mu]imp,\[Sigma]imp]
];




(* Perform a Monte-Carlo Simulation (only retains final price) *)
MonteCarlo[stock_,time_,intervals_,trials_]:=Module[
		{S0,St,\[Mu],\[Sigma],n,T,\[CapitalDelta]t,str,ND,Step},
	{S0,\[Mu],\[Sigma]}=stock;{n,T}={intervals,time};\[CapitalDelta]t=T/n//N;
	
	(* Functions/Definitions *)
	ND=NormalDistribution[];
	Step:=#*Exp[(\[Mu]-(\[Sigma]^2)/2)*\[CapitalDelta]t+\[Sigma]*RandomReal[ND]*Sqrt[\[CapitalDelta]t]]&;
	
	(* Algorithm *)
	str=StringJoin["Progress out of ",ToString[trials]," trials:"];
	PrintTemporary[str];
	St=Monitor[Table[Nest[Step,S0,n],{i,trials}],i];
	
	(* Return *)
	St=Round[N[St],0.01];
	St
];



(* Calculate Bias a Second Way *)
BiasJack[hist_]:=Module[{jack,M,i},
	M=Length[hist];
	jack=Table[Entropy[Drop[hist,{i}]],{i,1,M}];
	jack=Total[jack]*(M-1)/(M)
]


(* Calculate Entropy and relevant stats for symbol *)
StockEntropy[ticker_]:=Module[
		{prices,stock,trials,intervals,St,Bins,BinSpread,Ent,Bias,BiasJ,EntAdj},

	(* Step 1: get a year of closing data *)
	prices=FinancialData[ticker,"Close",DatePlus[{-1,"Year"}]];
	prices=FinancialData[ticker,"Close",{{2009,3,24},{2010,3,23}} ];
	prices=Part[prices,All,2];

	(* Step 2: estimate drift and diffusion terms *)
	stock=StockEst[prices];

	(* Step 3: starting from last price, simulate the next day with MC *)
	trials=1000000;
	intervals=1;
	St=MonteCarlo[stock,1,intervals,trials];

	(* Step 4: find spread of observed prices *)
	Bins=Length[DeleteDuplicates[St]];
	BinSpread=IntegerPart[Max[St]*100-Min[St]*100+1];

	(* Step 5: estimate entropy *)
	Ent=Entropy[2,St]//N;
	Bias=(BinSpread)/(2*trials)//N;
	EntAdj=Ent+Bias;

	(* Step 6: return values *)
	Flatten[{ticker,stock,Bins,BinSpread,Ent,Bias,EntAdj}]

];


(* ::Section:: *)
(*Joint Entropy*)


(* A single step of Monte Carlo for 2 correlated stocks *)

JointMCStep[stock1_,stock2_,corr_,time_]:=Module[
	{S0,\[Mu],\[Sigma],T,\[Rho],Z1,St1,Z2,St2},
	
	
T=time;
	
\[Rho]=corr;

Z1=RandomReal[NormalDistribution[]];
Z2=RandomReal[NormalDistribution[]];

{S0,\[Mu],\[Sigma]}=stock1;
St1=S0*Exp[(\[Mu]-(\[Sigma]^2)/2)*T+\[Sigma]*Z1*Sqrt[T]];
St1=Round[N[St1],0.01];

{S0,\[Mu],\[Sigma]}=stock2;
St2=S0*Exp[(\[Mu]-(\[Sigma]^2)/2)*T+\[Sigma]*(\[Rho]*Z1+Sqrt[1-\[Rho]^2]*Z2)*Sqrt[T]];
St2=Round[N[St2],0.01];

{St1,St2}

];


(* List of pairs of final values for 2 correlated stocks *)

JointMonteCarlo[stock1_,stock2_,corr_,time_,trials_]:=Module[
{str,St,i},

	str=StringJoin["Progress out of ",ToString[trials]," trials:"];
	PrintTemporary[str];
	St=Monitor[Table[JointMCStep[stock1,stock2,corr,time],{i,trials}],i];
	(*N[IntegerPart[St*100]/100]*)
	St
]


(* ::Section:: *)
(*Min Entropy*)


(* MinEntropy function which works exactly like Entropy[base,list] *)

MinEntropy[base_,list_]:=Module[
{n,maxFreq},
n=Length[list];
maxFreq=Max[Part[Tally[list],All,2]];
-Log[base,maxFreq/n]
]


(* Calculate Min Entropy for symbol *)
(* Use StockEntropy to get other relevant statistics *)
StockMinEntropy[ticker_]:=Module[
		{prices,stock,trials,intervals,St,Bins,BinSpread,Ent,Bias,BiasJ,EntAdj},

	(* Step 1: get a year of closing data *)
	prices=FinancialData[ticker,"Close",DatePlus[{-1,"Year"}]];
	prices=FinancialData[ticker,"Close",{{2009,3,24},{2010,3,23}} ];
	prices=Part[prices,All,2];

	(* Step 2: estimate drift and diffusion terms *)
	stock=StockEst[prices];

	(* Step 3: starting from last price, simulate the next day with MC *)
	trials=1000000;
	intervals=1;
	St=MonteCarlo[stock,1,intervals,trials];

	(* Step 4: estimate min entropy *)
	Ent=MinEntropy[2,St]//N;

	(* Step 5: return values *)
	Flatten[{ticker,Ent}]

];


(* ::Section:: *)
(*Other Functions*)


(* Full Monte-Carlo path *)
MonteCarloPath[stock_,time_,intervals_,trials_]:=Module[
			{S0,St,\[Mu],\[Sigma],n,T,\[CapitalDelta]t,ND,EulerStep},

	{S0,\[Mu],\[Sigma]}=stock;{n,T}={intervals,time};\[CapitalDelta]t=T/n//N;

	(* Functions/Definitions *)
	ND=NormalDistribution[];
	EulerStep:=#+\[Mu]*#*\[CapitalDelta]t+\[Sigma]*#*RandomReal[ND]*Sqrt[\[CapitalDelta]t]&;
	
	(* Algorithm *)
	St=Table[NestList[EulerStep,S0,n],{trials}];


	(* Return *)
	St
];




(* Use Euler-timestepping instead of analytic solution *)
MonteCarloEuler[stock_,time_,intervals_,trials_]:=Module[
		{S0,St,\[Mu],\[Sigma],n,T,\[CapitalDelta]t,ND,EulerStep},

	{S0,\[Mu],\[Sigma]}=stock;{n,T}={intervals,time};\[CapitalDelta]t=T/n//N;
	
	(* Functions/Definitions *)
	ND=NormalDistribution[];
	EulerStep:=#+\[Mu]*#*\[CapitalDelta]t+\[Sigma]*#*RandomReal[ND]*Sqrt[\[CapitalDelta]t]&;
	
	(* Algorithm *)
	St=Monitor[Table[Nest[EulerStep,S0,n],{i,trials}],i];
	
	(* Return *)
	St=Round[N[St],0.01];
	St
];



(* Return a single path simulation for one time period *)

MCIncrement[stock_,time_,intervals_]:=Module[{
		S0,St,\[Mu],\[Sigma],n,T,\[CapitalDelta]t,ND,Step},

	{S0,\[Mu],\[Sigma]}=stock;{n,T}={intervals,time};\[CapitalDelta]t=T/n//N;

	ND=NormalDistribution[];
	Step:=#*Exp[(\[Mu]-(\[Sigma]^2)/2)*\[CapitalDelta]t+\[Sigma]*RandomReal[ND]*Sqrt[\[CapitalDelta]t]]&;

	St=Nest[Step,S0,n];
	St=Round[N[St],0.01];
	St
];


(* ::Section:: *)
(*Done*)


Print["Library for stock price entropy loaded (Jeremy Clark, 2010, BSD License)."]
