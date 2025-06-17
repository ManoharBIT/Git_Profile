// File: full_adder_sva.sv
module full_adder_sva #(
    parameter WIDTH = 1
)(
    input  logic clk,
    input  logic [WIDTH-1:0] a,
    input  logic [WIDTH-1:0] b,
    input  logic             cin,
    input  logic [WIDTH-1:0] sum,
    input  logic             cout
);

    logic [WIDTH:0] expected;

    always_comb expected = a + b + cin;

    // Check entire sum and carry in one assertion
    property p_full_adder;
        @(posedge clk) ({cout, sum} == expected);
    endproperty

    assert_full_adder: assert property (p_full_adder)
        else $error("Assertion failed: {cout, sum} != a + b + cin");

endmodule
