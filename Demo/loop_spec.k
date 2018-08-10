module LOOP_SPEC
imports MIX
rule
<k> 

loop(S:Int)
=>
S
...
</k>
<env>
...
ENV:Map
...
</env>
<store>
...
STORE:Map
...
</store>
<fun>
...
FUN:Map
...
</fun>
<reg>
.Map=>Reg:Map
</reg>
<sreg>
.Map=>Sreg:Map
</sreg>
requires S>=Int 0


rule
<k>
add r 2, r 2, #1
add r 1, r 1, r 2
cmp r 0, r 2
BEQ END
B loop
END
=>
END
</k>
<fun>
...
FUN:Map
...
</fun>
<reg>
...
0 |-> S:Int
1 |-> (_:Int=>S1:Int)
2 |-> (_:Int=>S)
...

</reg>
<sreg>
...
0 |-> (_=>true)
...
</sreg>
requires S>=Int 0
endmodule
