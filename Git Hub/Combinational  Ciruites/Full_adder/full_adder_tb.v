// File: full_adder_tb.v
`timescale 1ns / 1ps

module full_adder_tb;

    parameter WIDTH = 4;

    reg  [WIDTH-1:0] a, b;
    reg              cin;
    wire [WIDTH-1:0] sum;
    wire             cout;

    full_adder #(.WIDTH(WIDTH)) dut (
        .a(a), .b(b), .cin(cin),
        .sum(sum), .cout(cout)
    );

    integer i;
    initial begin
        $display("Starting Full Adder TB");
        for (i = 0; i < (1 << (2*WIDTH)); i = i + 1) begin
            {a, b} = i;
            cin = i % 2;
            #5;
            $display("a=%b b=%b cin=%b --> sum=%b cout=%b", a, b, cin, sum, cout);
        end
        $finish;
    end
endmodule
