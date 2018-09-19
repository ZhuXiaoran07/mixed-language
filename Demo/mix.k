

module MIX-SYNTAX
  syntax AExp  ::= Int | String | Id 
                 | "++" Id
                 | FunctionCall
                 > AExp "/" AExp              [left, strict, division]
				 | AExp "*" AExp              [left, strict]
                 > AExp "+" AExp              [left, strict]
				 | AExp "-" AExp              [left, strict]
                 | "(" AExp ")"               [bracket]
				 
				 
  syntax BExp  ::= Bool
                 | AExp "<=" AExp             [seqstrict]
                 | "!" BExp                   [strict]
                 > BExp "&&" BExp             [left, strict(1)]
                 | "(" BExp ")"               [bracket]
				 
  syntax Block ::= "{" Stmts "}"
  
  syntax Stmt  ::=  Id "=" AExp";"                              [strict(2)]
                 | "if" "(" BExp ")" Block "else" Block         [strict(1)]
				 | "while" "(" BExp ")" Block
                 | Type Ids ";"
				 | FunctionCall ";"
				 | FunDef
				 | "return" AExp ";"                            [strict(1)]
				 | InsList
				 | Instr
				 
				 
 syntax BOpCode ::=  "sub" | "mul" | "div" | "orr" | "and"	
 syntax BInst   ::= BOpCode AExp "," AExp "," AExp  [strict(3)]
 syntax BInst   ::="add" AExp "," AExp "," AExp  [strict(2,3)]
 syntax JOpCode ::= "jmp" | "B" | "BL" | "BEQ"
 syntax JInst   ::= JOpCode Id | JOpCode "END"
 syntax MOpCode ::= "ldr" | "str" | "stmdb" | "stmib" | "ldmia" | "mrs" | "msr" | "mov" | "cmp"
 syntax MInst   ::= MOpCode  Reg "," AExp  [seqstrict(3)]
 //syntax InsList ::= "_asm_"	"{" InlInstrs"}"	
 syntax Instr    ::= BInst | JInst | MInst | "END"

 syntax FunctionCall::= Id "(" AExps")" 
//[strict(2)]	

syntax Param::=Type Id
syntax Type::="int" | "void"
syntax Params::=List{Param, ","}
syntax VariDecls::=List{Param, ";"}

syntax FunDef::=FunctionDef Block
syntax FunctionDef::= Type Id "("Params ")"
syntax Id ::= "main" | "sum" | "g" | "loop" | "Schedule" | "DisableAllInterrupts" | "EnableAllInterrupts"

			  

  //syntax Stmt ::= InlInstr | AssCall	
  syntax Stmt ::= AssCall	
  syntax AssCall::=  Id Instrs  
 // syntax Instr ::= "add" Reg "," AExp "," AExp  [strict(2, 3)]
 //				 | "sub" Reg "," AExp "," AExp  [strict(2, 3)]
//               | "ldr" Reg "," AExp		    [strict(2)]	
//				 | "str" Reg "," AExp          
//				 | "B"   Id
//				 | "BL"  Id
//                | "END"
							 
  syntax AExp   ::= "#" Int
                 | Stack
                 | Reg
  syntax Stack ::= "[" "SP" "]"
				 | "[" "SP" "," AExp "]"
  syntax Reg    ::= "r" Int	
  
  syntax InsList ::= "__asm"	"{" Instrs"}" 
// syntax InsList ::= "__asm"	"{" InlInstrs"}" 
// syntax InlInstr ::= "add" AExp "," AExp "," AExp  [seqstrict(2, 3)]
//				   | "sub" AExp "," AExp "," AExp  [seqstrict(2, 3)]
//				   | Instr 
					 
					 
  syntax Ids      ::= List{Id,","}
  syntax AExps    ::= List{AExp,","} //[seqstrict]
  syntax Stmts    ::= List{Stmt,""}
  syntax Ints     ::= List{Int, ""}
  syntax Instrs   ::= List{Instr, ""}
//  syntax InlInstrs::= List{InlInstr, ""}
endmodule


module MIX
  imports MIX-SYNTAX
  syntax KResult ::= Int | Bool
  syntax KItem ::="execute"
  
  configuration <T>
            <k> $PGM:Stmts~>execute </k> //statements to be executed
            <env>.Map</env>              //maps variable names into locations
			<store>.Map</store>          //maps locations into values
			<loc> 0 </loc>
            <fun>.Map</fun>              //maps function name to function body and parameter
            <fstack> .List </fstack>     //store context for function call         
            <reg> .Map </reg>
			<sreg> .Map </sreg>
			<stack> .List </stack>
            </T>

// AExp
  rule <k> X:Id => I ...</k>
       <env>... X |-> N ...</env>
       <store>... N |-> I ...</store>  [lookup]
  rule <k> ++X => I +Int 1 ...</k>
       <env>... X |-> N ...</env>
       <store>... N |-> (I => I +Int 1) ...</store>  [increment]
  
  rule I1 / I2 => I1 /Int I2  requires I2 =/=Int 0
  rule I1 * I2 => I1 *Int I2
  rule I1 + I2 => I1 +Int I2
  rule I1 - I2 => I1 -Int I2
  rule Str1 + Str2 => Str1 +String Str2
// BExp
  rule I1 <= I2 => I1 <=Int I2
  rule ! T => notBool T
  rule true && BE => BE
  rule false && _ => false
// Block
  rule <k> {Ss} => Ss ~> Rho ...</k> <env> Rho </env>  [structural]
  rule <k> Rho => . ...</k> <env> _ => Rho </env>    [structural]
// Stmt
 
  rule <k> X = I:Int; =>. ...</k>
       <env>... X |-> N ...</env>
       <store>... N |-> (_ => I) ...</store>  [assignment]
  rule if (true)  S else _ => S
  rule if (false) _ else S => S
  rule while (BE) {S} => if (BE) {S while (BE) {S}} else {.Stmts}  [structural]

  rule .AExps => .
  rule <k> int (X,Xs => Xs); ...</k>
       <env> Rho => Rho(X|-> L) </env>
       <store>... .Map => L |-> 0 ...</store>
	   <loc> L => L +Int 1 </loc>
  rule int .Ids; => .  [structural]

  syntax KItem ::= "functionBody""(" Params"," Type"," Stmts")"
                 | "functionBody""(" Instrs ")"
  
  // auxiliary function
  syntax KItem::="(" Map ","  K ")"	
				|"(" List "," K ")"
  syntax KItem ::= mkDecls(Params,AExps)  [function]

  rule mkDecls((T:Type X:Id, Ps:Params), (V:AExp, Vs:AExps))
    => T:Type X;~>X=V;~> mkDecls(Ps,Vs)

	
  rule mkDecls(.Params,.AExps) => .K
  
  
 // Function Defintion
 rule
     <k>(T:Type F:Id(Ps:Params) {Ss:Stmts})=>. ...</k>
	 <fun> ... .Map=>F|->functionBody(Ps, T, Ss) ...</fun>
	 
 // main function call	 
 rule <k> execute =>Ps ~> Ss </k>
      <env> Env:Map=>.Map </env>
      <fun> ... main |-> functionBody(Ps, T:Type, Ss) ... </fun>
	  <fstack> .List =>ListItem((Env, .K)) </fstack>
	  
 rule <k> execute => Ins </k>
      <fun> ... main |-> functionBody(Ins) ... </fun>
	 
 
 // Function Call
 rule
     <k>(F1:Id(As:AExps)~>K) =>(mkDecls(Ps, As)~>Ss)</k>
	 <env> Env:Map</env>
     <fstack> .List => ListItem((Env, K)) ...</fstack>
	 <fun> ...F1|->functionBody(Ps:Params, _:Type, Ss:Stmts)
    ...</fun>
	
  // return	to C
  rule
	 <k>return I:Int;~>_ =>I~>K</k>
	 <env>_=>Env</env>
	 <fstack> ListItem((Env, K)) => .List ...</fstack>
	 
  

 rule <k> F:Id Is:Instrs=>. ...</k>
      <fun> ... .Map=>  F|->functionBody(Is) ... </fun>

// auxiliary instructions
syntax Instr ::= "stm" Stack "," AExp         [strict(2)]
			   | "ldm" Stack "," AExp    
			   
syntax KItem ::= AssReg(AExps, Int)  [function]
rule AssReg((A:AExp, As:AExps), I)
  => ldr r I, A~> AssReg(As:AExps, I+Int 1)  
     when I <=Int 3
	 
rule AssReg((A:AExp, As:AExps), I)
  => stm [SP], A~>AssReg(As:AExps, I+Int 1)  
     when I >=Int 4
	 
rule AssReg(.AExps, I)=>.

// Assembler Function Defintion
rule 
     <k> F:Id Is:Instrs END=>. ...</k>
     <fun> ... .Map=>  F|->functionBody(Is) ... </fun>
	 
// Assembler Function Call
rule 
    <k>(F1:Id(As:AExps)~>K) =>(AssReg(As, 0)~>Is~>END)</k>
    <fstack> .List => ListItem((Env, K)) ...</fstack>
	<fun> ...F1|->functionBody(Is)...</fun>
	<env> Env:Map </env>
	
syntax KItem ::= AssReg(AExps, Int)  [function]

rule 
     AssReg((A:AExp, As:AExps), I) 
  => ldr r I, A~> AssReg(As:AExps, I+Int 1) 
	when I <=Int 3
rule 
     AssReg((A:AExp, As:AExps), I)
 => stm [SP], A~>AssReg(As:AExps, I+Int 1) 
    when I >=Int 4
	
rule AssReg(.AExps, I)=>.
	



// Stmts
  rule .Stmts => .                 [structural]
  rule S:Stmt Ss:Stmts => S ~> Ss  [structural]

  syntax Int ::= lookup( List, Int ) [function]
  rule lookup(ListItem(I) L, 0) => I
  rule lookup(ListItem(I) L, I1) => lookup(L, I1-Int 4) requires I1 >Int 0
  rule lookup(.List, I) => 0
  
//assembly  
  rule <k> r I:Int => I2:Int ...</k>
       <reg>... I |-> I2 ...</reg>
	   
  rule <k> r I:Int => 0 ... </k>
       <reg> R:Map => R[I <- 0]</reg>
	   when notBool I in keys(R)
  
   rule # I:Int => I [macro]
   rule [SP]=> [SP, 0] [macro]
   rule <k> [SP, I1] => lookup(L, I1) ...</k>
        <stack> L </stack>
  
  // load a value to a register  
  rule
      <k> ldr r I:Int , I1:Int =>. ...</k>
      <reg> R:Map => R[I <- I1] </reg>
	  
  // store a value to the memory
  rule 
      <k> str r I, X => . ... </k>
	  <reg>... I |-> I1 ...</reg>
      <env> ... X |-> L:Int ... </env>
      <store> ... L |-> (_ => I1) ... </store>
	 
	  
   rule   
	   <k> str r I, [SP, -4] => . ... </k>
	   <reg> ... I |-> I2 ... </reg>
	   <stack> L => ListItem(I2) L </stack>
	  
  // add instruction
  rule 
      <k> add r I:Int , I2:Int , I3:Int =>. ...</k>
      <reg> R:Map => R[I <- I2 +Int I3] </reg>
	  
	  
  rule __asm{Is:Instrs} =>Is

  rule 
      <k> add X:Id , I2:Int , I3:Int =>. ...</k>
      <env> ... X |-> LX ... </env>
	  <store> ... LX |-> (_ => (I2 +Int I3)) ... </store>
   rule 
      <k> sub X:Id , I2:Int , I3:Int =>. ...</k>
      <env> ... X |-> LX ... </env>
	  <store> ... LX |-> (_ => (I2 -Int I3)) ... </store>
	
  // push	
  rule <k> stm [SP], I:Int => . ...</k>
       <stack>L:List=> ListItem(I) L </stack>
  // pop
  rule <k> ldm [SP], X:Id =>. ...</k>
       <stack> ListItem(I) L => L</stack>
	   <env> ... X |-> I2 ... </env>
	   <store> ... I2 |-> (_ => I) ...</store>
  	   
  rule <k> sub r I:Int , I2:Int , I3:Int =>. ...</k>
       <reg> R:Map => R[I <- I2 -Int I3] </reg>
  rule <k> ldr r I:Int , I1:Int =>. ...</k>
       <reg> R:Map => R[I <- I1] </reg>
	   
  // jump instructions
  rule <k> B X:Id ~> _ => Is  </k>
       <fun> ... X |-> functionBody(Is) ... </fun>
	  // <fstack> .List => ListItem((.K)) ...</fstack>
	   
  rule <k> BL X:Id ~> K =>Is ~>END </k>
       <fun> ... X |-> functionBody(Is) ... </fun>
	   <fstack> .List => ListItem((K)) ...</fstack>
	   
  rule <k> orr r I:Int , I2:Int , I3:Int =>. ...</k>
       <reg> R:Map => R[I <- I2 |Int I3] </reg>
	   
  rule <k> and r I:Int , I2:Int , I3:Int =>. ...</k>
       <reg> R:Map => R[I <- I2 &Int I3] </reg>
	   
  rule <k> cmp r I:Int , I1:Int => . ...</k>
       <reg> ... I|-> I2 ... </reg>
       <sreg> R:Map=> R[0<-(I2 ==Int I1)]  </sreg>
	   
   rule <k> BEQ END => . ... </k>
        <sreg> ... 0 |-> false ... </sreg>
		
   rule <k> (BEQ END) => (B END)... </k> 
        <sreg> ... 0 |-> true ... </sreg>
	   
	   
  syntax KItem ::= AssPara(Params, Int)  [function]
  rule AssPara((T:Type X:Id, Ps:Params), N:Int) 
       => T:Type X;~> str r N, X ~> AssPara(Ps, N+Int 1) requires N <=Int 3
  rule AssPara((T:Type X:Id, Ps:Params), N:Int)
       => T:Type X;~> ldm [SP], X ~> AssPara(Ps, N+Int 1) requires N >Int 3
  rule AssPara(.Params, N) => .
   
   // assembler call C function
   /*rule 
        <k> B X:Id ~> _ => AssPara(Ps, 0) ~> Ss </k>
        <fun> ...X|->functionBody(Ps:Params, _:Type, Ss:Stmts)...</fun>
      //  <fstack> .List => ListItem((.K)) ...</fstack>
	*/	
	rule 
	   <k> BL X:Id ~> K => AssPara(Ps, 0) ~> Ss  </k>
       <fun> ...X|->functionBody(Ps:Params, _:Type, Ss:Stmts)...</fun>
	   <fstack> .List => ListItem((K)) ...</fstack>

    rule 
       <k> B END ~> _ => END </k>
     //  requires X==K END 
	  
		   
    // return to assembly 
  /*  rule 
	   <k>return I:Int;~>_ =>ldr r 0, I~>K</k>
	   <fstack> ListItem((K)) L => L</fstack> 	   
	  */	
	// Assembler Function Return
    rule 
       <k> END ~>_ =>I~>K</k>
	   <env>_=>Env</env>
	   <reg>... 0|-> I ...</reg>
	   <fstack> ListItem((Env,  K)) => .List ...</fstack>
	
	// assembly call C variable 
	
	
endmodule
