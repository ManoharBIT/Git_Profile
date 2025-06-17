//===========================   
// File: full_adder_uvm_sva.sv   
//===========================   
//---------------------------------------------   
// Interface   
//--------------------------------------------- 
interface full_adder_if(input bit clk);   logic 
a, b, cin, sum, carry; endinterface   
//---------------------------------------------   
// DUT - Full Adder   
//---------------------------------------------   
module full_adder(input logic a, b, cin, output logic sum, carry);    
assign {carry, sum} = a + b + cin; endmodule   
//---------------------------------------------   
// Testbench   
//---------------------------------------------  
module tb;    bit clk = 0;   always 
#5 clk = ~clk;   full_adder_if 
fa_if(clk);   
full_adder DUT(   
.a(fa_if.a), .b(fa_if.b), .cin(fa_if.cin),   
.sum(fa_if.sum), .carry(fa_if.carry)   
);   
initial 
begin      
run_test("full_adder_test");   end 
endmodule //--------------- ------------------------------   
// UVM Sequence Item   
//---------------------------------------------   
class full_adder_tx extends uvm_sequence_item;    
rand bit a, b, cin;   
bit 
`uvm_object_utils(full_adder_tx)   
new(string 
name 
= 
sum, carry;   
function 
"full_adder_tx");     
super.new(name);   endfunction endclass   
//---------------------------------------------   
// UVM Sequence   
//---------------------------------------------   
class full_adder_seq extends uvm_sequence #(full_adder_tx);    
`uvm_object_utils(full_adder_seq)   function new(string name 
= "full_adder_seq");     
body();     
super.new(name);   endfunction   task 
full_adder_tx tx;     
repeat (10) begin       
full_adder_tx::type_id::create("tx");       
tx = 
assert(tx.randomize());       
start_item(tx);       
finish_item(tx);     
//---------------------------------------------   
// UVM Driver   
//---------------------------------------------   
end   endtask endclass   
class full_adder_driver extends uvm_driver #(full_adder_tx);    
virtual full_adder_if vif;   
`uvm_component_utils(full_adder_driver)    
new(string 
name, 
uvm_component 
super.new(name, parent);   
function 
void 
endfunction    
function 
parent);     
virtual 
build_phase(uvm_phase phase);     
super.build_phase(phase);   
if (!uvm_config_db #(virtual full_adder_if)::get(this, "", "vif", vif))   
`uvm_fatal("NOVIF", "No interface")   
endfunction   
run_phase(uvm_phase phase);      
forever begin       
full_adder_tx tx;       
seq_item_port.get_next_item(tx);       
= tx.a; vif.b = tx.b; vif.cin = tx.cin;       
@(posedge vif.clk);       
seq_item_port.item_done();     end   
task 
vif.a 
endtask endclass  //---------------------------------------------   
 
// UVM Monitor   
//---------------------------------------------   
class full_adder_monitor extends uvm_component;    
virtual full_adder_if vif;   uvm_analysis_port  
#(full_adder_tx) mon_port;    
`uvm_component_utils(full_adder_monitor)   function 
new(string name, uvm_component parent);     
super.new(name, parent);     mon_port = 
new("mon_port", this);   endfunction   
  virtual function void build_phase(uvm_phase phase);     super.build_phase(phase);   
    if (!uvm_config_db #(virtual full_adder_if)::get(this, "", "vif", vif))   
      `uvm_fatal("NOVIF", "No interface")   
endfunction   task 
run_phase(uvm_phase phase);   
    full_adder_tx tx;     forever 
begin       @(posedge 
vif.clk);   
      tx = full_adder_tx::type_id::create("tx");        
tx.a = vif.a; tx.b = vif.b; tx.cin = vif.cin;       
tx.sum = vif.sum; tx.carry = vif.carry;       
mon_port.write(tx);     end   endtask endclass   
   
//---------------------------------------------   
// UVM Scoreboard   
//---------------------------------------------   
class full_adder_scoreboard extends uvm_component;   
`uvm_component_utils(full_adder_scoreboard)    uvm_analysis_imp 
#(full_adder_tx, full_adder_scoreboard) sb_port;   function 
new(string name, uvm_component parent);     super.new(name, 
parent);     sb_port = new("sb_port", this);   endfunction   
  function void write(full_adder_tx tx);     bit 
expected_sum, expected_carry;      
{expected_carry, expected_sum} = tx.a + 
tx.b + tx.cin;     if  
(tx.sum !== expected_sum || tx.carry !== expected_carry)   
      `uvm_error("Adder SB", $sformatf("Mismatch: a=%0b b=%0b cin=%0b sum=%0b carry=%0b (Expected: sum=%0b 
carry=%0b)",   
                 tx.a, tx.b, tx.cin, tx.sum, tx.carry, expected_sum, expected_carry))    
endfunction endclass   
//---------------------------------------------   
// UVM Agent   
//---------------------------------------------   
class full_adder_agent extends uvm_component;   
`uvm_component_utils(full_adder_agent)   full_adder_driver 
drv;   full_adder_monitor mon;   
function new(string name, uvm_component parent);      
super.new(name, parent);   
endfunction   
virtual function void build_phase(uvm_phase phase);     super.build_phase(phase);     
drv =  
full_adder_driver::type_id::create("drv", this);     
mon = 
full_adder_monitor::type_id::create("mon", this);   endfunction 
endclass   
//---------------------------------------------   
// UVM Environment   
//---------------------------------------------   
class 
full_adder_env 
extends 
`uvm_component_utils(full_adder_env)   
uvm_env;   
full_adder_agent agent;   full_adder_scoreboard sb;   
function new(string name, uvm_component parent);     
super.new(name, parent);   endfunction   
virtual function void build_phase(uvm_phase phase);     
agent = full_adder_agent::type_id::create("agent", this);     
= full_adder_scoreboard::type_id::create("sb", this);   
endfunction   
virtual function void connect_phase(uvm_phase phase);      
sb 
agent.mon.mon_port.connect(sb.sb_port);   endfunction endclass   
//---------------------------------------------   
// UVM Test   
//---------------------------------------------   
class 
full_adder_test 
extends 
`uvm_component_utils(full_adder_test)   
uvm_test;   
full_adder_env env;   full_adder_seq seq;   function 
 
new(string name, uvm_component parent);     
super.new(name, parent);   endfunction   
  virtual function void build_phase(uvm_phase phase);      
env = full_adder_env::type_id::create("env", this);    
endfunction   
  task run_phase(uvm_phase phase);     
phase.raise_objection(this);     seq = 
full_adder_seq::type_id::create("seq");     seq.start(env.agent.drv);      
phase.drop_objection(this);   endtask endclass   
   
//---------------------------------------------   
// SVA Checker   
//---------------------------------------------   
module full_adder_checker(    
input logic a, b, cin,    
input logic sum, carry   
);   
  property full_adder_check;     sum + 
(carry << 1) == a + b + cin;   
endproperty   
  assert property (full_adder_check); endmodule   