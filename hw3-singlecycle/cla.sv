`timescale 1ns / 1ps

/**
 * @param a first 1-bit input
 * @param b second 1-bit input
 * @param g whether a and b generate a carry
 * @param p whether a and b would propagate an incoming carry
 */
module gp1 (
    input  wire a,
    b,
    output wire g,
    p
);
  assign g = a & b;
  assign p = a | b;
endmodule

/**
 * Computes aggregate generate/propagate signals over a 4-bit window.
 * @param gin incoming generate signals
 * @param pin incoming propagate signals
 * @param cin the incoming carry
 * @param gout whether these 4 bits internally would generate a carry-out (independent of cin)
 * @param pout whether these 4 bits internally would propagate an incoming carry from cin
 * @param cout the carry outs for the low-order 3 bits
 */
module gp4 (
    input wire [3:0] gin,
    pin,
    input wire cin,
    output wire gout,
    pout,
    output wire [2:0] cout
);

  assign cout[0] = gin[0] | (pin[0] & cin);
  assign cout[1] = gin[1] | (pin[1] & (gin[0] | (pin[0] & cin)));
  assign cout[2] = gin[2] | (pin[2] & (gin[1] | (pin[1] & (gin[0] | (pin[0] & cin)))));

  assign gout = gin[3] | (pin[3] & gin[2]) | (pin[3] & pin[2] & gin[1]) | (pin[3] & pin[2] & pin[1] & gin[0]);
  assign pout = pin[0] & pin[1] & pin[2] & pin[3];

endmodule

/** Same as gp4 but for an 8-bit window instead */
module gp8 (
    input wire [7:0] gin,
    pin,
    input wire cin,
    output wire gout,
    pout,
    output wire [6:0] cout
);

  assign cout[0] = gin[0] | (pin[0] & cin);
  assign cout[1] = gin[1] | (pin[1] & (gin[0] | (pin[0] & cin)));
  assign cout[2] = gin[2] | (pin[2] & (gin[1] | (pin[1] & (gin[0] | (pin[0] & cin)))));
  assign cout[3] = gin[3] | (pin[3] & (gin[2] | (pin[2] & (gin[1] | (pin[1] & (gin[0] | (pin[0] & cin)))))));
  assign cout[4] = gin[4] | (pin[4] & (gin[3] | (pin[3] & (gin[2] | (pin[2] & (gin[1] | (pin[1] & (gin[0] | (pin[0] & cin)))))))));
  assign cout[5] = gin[5] | (pin[5] & (gin[4] | (pin[4] & (gin[3] | (pin[3] & (gin[2] | (pin[2] & (gin[1] | (pin[1] & (gin[0] | (pin[0] & cin)))))))))));
  assign cout[6] = gin[6] | (pin[6] & (gin[5] | (pin[5] & (gin[4] | (pin[4] & (gin[3] | (pin[3] & (gin[2] | (pin[2] & (gin[1] | (pin[1] & (gin[0] | (pin[0] & cin)))))))))))));

  assign gout = gin[7] | (pin[7] & gin[6]) | (pin[7] & pin[6] & gin[5]) | (pin[7] & pin[6] & pin[5] & gin[4]) | (pin[7] & pin[6] & pin[5] & pin[4] & gin[3]) | (pin[7] & pin[6] & pin[5] & pin[4] & gin[3]) | (pin[7] & pin[6] & pin[5] & pin[4] & gin[3]) | (pin[7] & pin[6] & pin[5] & pin[4] & pin[3] & gin[2]) | (pin[7] & pin[6] & pin[5] & pin[4] & pin[3] & pin[2] & gin[1]) | (pin[7] & pin[6] & pin[5] & pin[4] & pin[3] & pin[2] & pin[1] & gin[0]);
  assign pout = pin[0] & pin[1] & pin[2] & pin[3] & pin[4] & pin[5] & pin[6] & pin[7];

endmodule

module cla (
    input  wire [31:0] a,
    b,
    input  wire        cin,
    output wire [31:0] sum
);

  wire [31:0] g, p;
  wire [3:0] gout, pout;
  wire [7:0] gin[3:0], pin[3:0];
  wire [6:0] cout[3:0];
  wire [3:0] next_cin;

  genvar i;
  for (i = 0; i < 32; i++) begin : gp1_bits
    gp1 gp_bit (
        .a(a[i]),
        .b(b[i]),
        .g(g[i]),
        .p(p[i])
    );
  end

  for (i = 0; i < 4; i++) begin
    assign gin[i] = g[i*8+:8];
    assign pin[i] = p[i*8+:8];
  end

  assign next_cin[0] = cin;

  wire [6:0] temp_cout0;
  gp8 gp_block0 (
      .gin (gin[0]),
      .pin (pin[0]),
      .cin (next_cin[0]),
      .gout(gout[0]),
      .pout(pout[0]),
      .cout(temp_cout0)
  );
  assign cout[0] = temp_cout0;
  wire next_cin1 = gout[0] | (pout[0] & cin);

  wire [6:0] temp_cout1;
  gp8 gp_block1 (
      .gin (gin[1]),
      .pin (pin[1]),
      .cin (next_cin1),
      .gout(gout[1]),
      .pout(pout[1]),
      .cout(temp_cout1)
  );
  assign cout[1] = temp_cout1;
  wire next_cin2 = gout[1] | (pout[1] & next_cin1);

  wire [6:0] temp_cout2;
  gp8 gp_block2 (
      .gin (gin[2]),
      .pin (pin[2]),
      .cin (next_cin2),
      .gout(gout[2]),
      .pout(pout[2]),
      .cout(temp_cout2)
  );
  assign cout[2] = temp_cout2;
  wire next_cin3 = gout[2] | (pout[2] & next_cin2);

  wire [6:0] temp_cout3;
  gp8 gp_block3 (
      .gin (gin[3]),
      .pin (pin[3]),
      .cin (next_cin3),
      .gout(gout[3]),
      .pout(pout[3]),
      .cout(temp_cout3)
  );
  assign cout[3] = temp_cout3;

  generate
    for (i = 0; i < 32; i++) begin : sums
      if (i % 8 == 0) begin : sum_assign
        assign sum[i] = a[i] ^ b[i] ^ (i == 0 ? cin : (i == 8 ? next_cin1 : (i == 16 ? next_cin2 : next_cin3)));
      end else begin : sum_assign_else
        assign sum[i] = a[i] ^ b[i] ^ cout[i/8][i%8-1];
      end
    end
  endgenerate

endmodule
