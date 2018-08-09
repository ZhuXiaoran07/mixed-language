module LOOP_SPEC
imports MIX
rule
<k> 

loop(S:Int)
=>
.
</k>
<env>
...
S|->LS
...
</env>
<store>
...
LS|->S=>N
...
</store>
requires S>=Int 0
endmodule
