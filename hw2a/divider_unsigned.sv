/* INSERT NAME AND PENNKEY HERE */

`timescale 1ns / 1ns

// quotient = dividend / divisor

module divider_unsigned (
    input  wire [31:0] i_dividend,
    input  wire [31:0] i_divisor,
    output wire [31:0] o_remainder,
    output wire [31:0] o_quotient
);

  // TODO: your code here
  wire [32:0][31:0] c_dividend;
  wire [32:0][31:0] c_remainder;
  wire [32:0][31:0] c_quotient;
  assign c_dividend[0]  = i_dividend;
  assign c_remainder[0] = 32'b0;
  assign c_quotient[0]  = 32'b0;

  genvar i;
  for (i = 0; i < 32; i = i + 1) begin
    divu_1iter divu_1iter_inst (
        .i_dividend (c_dividend[i]),
        .i_divisor  (i_divisor),
        .i_remainder(c_remainder[i]),
        .i_quotient (c_quotient[i]),
        .o_dividend (c_dividend[i+1]),
        .o_remainder(c_remainder[i+1]),
        .o_quotient (c_quotient[i+1])
    );
  end

  assign o_remainder = c_remainder[32];
  assign o_quotient  = c_quotient[32];

endmodule


module divu_1iter (
    input  wire [31:0] i_dividend,
    input  wire [31:0] i_divisor,
    input  wire [31:0] i_remainder,
    input  wire [31:0] i_quotient,
    output wire [31:0] o_dividend,
    output wire [31:0] o_remainder,
    output wire [31:0] o_quotient
);
  //first line remainder = (remainder << 1) | ((dividend >> 31) & 0x1)
  wire [31:0] r_temp1;
  wire [31:0] dividend_temp1;
  wire [31:0] dividend_temp2;
  wire [31:0] rem1;
  assign r_temp1 = {i_remainder[30:0], 1'b0};
  assign dividend_temp1 = {31'b0, i_dividend[31]};
  assign dividend_temp2 = dividend_temp1 & 32'b1;
  assign rem1 = r_temp1 | dividend_temp2;

  //quotient lshift for future use
  wire [31:0] quotient_lshift;
  assign quotient_lshift = {i_quotient[30:0], 1'b0};

  //first part of the if statement 
  wire [31:0] o_quotient1;
  wire [31:0] o_remainder1;
  assign o_quotient1  = quotient_lshift | 32'b1;
  assign o_remainder1 = rem1 - i_divisor;

  //second part of the if statement
  wire [31:0] o_quotient2;
  wire [31:0] o_remainder2;
  assign o_quotient2  = quotient_lshift | 32'b0;
  assign o_remainder2 = rem1;


  //muxing over the results based on if condition is positive
  assign o_quotient   = (rem1 >= i_divisor) ? o_quotient1 : o_quotient2;
  assign o_remainder  = (rem1 >= i_divisor) ? o_remainder1 : o_remainder2;

  //dividend = dividend << 1    
  assign o_dividend   = {i_dividend[30:0], 1'b0};



  /*
    for (int i = 0; i < 32; i++) {
        remainder = (remainder << 1) | ((dividend >> 31) & 0x1);
        if (remainder < divisor) {
            quotient = (quotient << 1);
        } else {
            quotient = (quotient << 1) | 0x1;
            remainder = remainder - divisor;
        }
        dividend = dividend << 1;
    }
    */

endmodule
