`timescale 1ns / 1ns

// registers are 32 bits in RV32
`define REG_SIZE 31:0

// insns are 32 bits in RV32IM
`define INSN_SIZE 31:0

// RV opcodes are 7 bits
`define OPCODE_SIZE 6:0

`ifndef RISCV_FORMAL
`include "../hw2b/cla.sv"
`include "../hw3-singlecycle/RvDisassembler.sv"
`include "../hw4-multicycle/divider_unsigned_pipelined.sv"
`endif

module Disasm #(
    byte PREFIX = "D"
) (
    input wire [31:0] insn,
    output wire [(8*32)-1:0] disasm
);
  // synthesis translate_off
  // this code is only for simulation, not synthesis
  string disasm_string;
  always_comb begin
    disasm_string = rv_disasm(insn);
  end
  // HACK: get disasm_string to appear in GtkWave, which can apparently show only wire/logic. Also,
  // string needs to be reversed to render correctly.
  genvar i;
  for (i = 3; i < 32; i = i + 1) begin : gen_disasm
    assign disasm[((i+1-3)*8)-1-:8] = disasm_string[31-i];
  end
  assign disasm[255-:8] = PREFIX;
  assign disasm[247-:8] = ":";
  assign disasm[239-:8] = " ";
  // synthesis translate_on
endmodule

module RegFile (
    input logic [4:0] rd,
    input logic [`REG_SIZE] rd_data,
    input logic [4:0] rs1,
    output logic [`REG_SIZE] rs1_data,
    input logic [4:0] rs2,
    output logic [`REG_SIZE] rs2_data,

    input logic clk,
    input logic we,
    input logic rst
);
  // TODO: copy your RegFile code here
  localparam int NumRegs = 32;
  logic [`REG_SIZE] regs[NumRegs];
  assign regs[0]  = 32'd0;
  assign rs1_data = regs[rs1];
  assign rs2_data = regs[rs2];
  always_ff @(posedge clk) begin
    if (rst) begin
      for (int i = 1; i < NumRegs; i = i + 1) begin
        regs[i] <= 32'd0;
      end
    end else begin
      for (int i = 1; i < NumRegs; i = i + 1) begin
        if (we && rd == i[4:0]) begin
          regs[i] <= rd_data;
        end
      end
    end
  end

endmodule

/** NB: ARESETn is active-low, i.e., reset when this input is ZERO */
interface axi_clkrst_if (
    input wire ACLK,
    input wire ARESETn
);
endinterface

interface axi_if #(
      parameter int ADDR_WIDTH = 32
    , parameter int DATA_WIDTH = 32
);
  logic                      ARVALID;
  logic                      ARREADY;
  logic [    ADDR_WIDTH-1:0] ARADDR;
  logic [               2:0] ARPROT;

  logic                      RVALID;
  logic                      RREADY;
  logic [    DATA_WIDTH-1:0] RDATA;
  logic [               1:0] RRESP;

  logic                      AWVALID;
  logic                      AWREADY;
  logic [    ADDR_WIDTH-1:0] AWADDR;
  logic [               2:0] AWPROT;

  logic                      WVALID;
  logic                      WREADY;
  logic [    DATA_WIDTH-1:0] WDATA;
  logic [(DATA_WIDTH/8)-1:0] WSTRB;

  logic                      BVALID;
  logic                      BREADY;
  logic [               1:0] BRESP;

  modport manager(
      input ARREADY, RVALID, RDATA, RRESP, AWREADY, WREADY, BVALID, BRESP,
      output ARVALID, ARADDR, ARPROT, RREADY, AWVALID, AWADDR, AWPROT, WVALID, WDATA, WSTRB, BREADY
  );
  modport subord(
      input ARVALID, ARADDR, ARPROT, RREADY, AWVALID, AWADDR, AWPROT, WVALID, WDATA, WSTRB, BREADY,
      output ARREADY, RVALID, RDATA, RRESP, AWREADY, WREADY, BVALID, BRESP
  );
endinterface

module MemoryAxiLite #(
    parameter int NUM_WORDS  = 32,
    //parameter int ADDR_WIDTH = 32,
    parameter int DATA_WIDTH = 32
) (
    axi_clkrst_if axi,
    axi_if.subord insn,
    axi_if.subord data
);

  // memory is an array of 4B words
  logic [DATA_WIDTH-1:0] mem_array[NUM_WORDS];
  localparam int AddrMsb = $clog2(NUM_WORDS) + 1;
  localparam int AddrLsb = 2;

  // [BR]RESP codes, from Section A 3.4.4 of AXI4 spec
  localparam bit [1:0] ResponseOkay = 2'b00;
  // localparam bit [1:0] ResponseSubordinateError = 2'b10;
  // localparam bit [1:0] ResponseDecodeError = 2'b11;

`ifndef FORMAL
  always_comb begin
    // memory addresses should always be 4B-aligned
    assert (!insn.ARVALID || insn.ARADDR[1:0] == 2'b00);
    assert (!data.ARVALID || data.ARADDR[1:0] == 2'b00);
    assert (!data.AWVALID || data.AWADDR[1:0] == 2'b00);
    // we don't use the protection bits
    assert (insn.ARPROT == 3'd0);
    assert (data.ARPROT == 3'd0);
    assert (data.AWPROT == 3'd0);
  end
`endif

  // TODO: changes will be needed throughout this module

reg insn_read_addr_valid = 1;

always_ff @(posedge axi.ACLK) begin
        if (!axi.ARESETn) begin
            insn.ARREADY <= 1'b1;
            data.ARREADY <= 1'b1;
            data.AWREADY <= 1'b1;
            data.WREADY <= 1'b1;
            insn.RVALID <= 1'b0;
            data.RVALID <= 1'b0;
            data.BVALID <= 1'b0;

        end else begin

            // insn read
            if (insn.ARVALID && insn.ARREADY) begin
              insn.RDATA <= mem_array[insn.ARADDR[AddrMsb:AddrLsb]];
              insn.RVALID <= 1'b1;
            end else begin
              insn.RVALID <= 1'b0;
            end


          // data read
            if (data.ARVALID && data.ARREADY) begin
              data.RDATA <= mem_array[data.ARADDR[AddrMsb:AddrLsb]];
              data.RVALID <= 1'b1;
            end else begin
              data.RVALID <= 1'b0;
            end


            // data write
            if (data.AWVALID && data.AWREADY && data.WVALID && data.WREADY) begin
              if (data.WSTRB[0]) begin
                mem_array[data.AWADDR[AddrMsb:AddrLsb]][7:0] <= data.WDATA[7:0];
              end
              if (data.WSTRB[1]) begin
                mem_array[data.AWADDR[AddrMsb:AddrLsb]][15:8] <= data.WDATA[15:8];
              end
              if (data.WSTRB[2]) begin
                mem_array[data.AWADDR[AddrMsb:AddrLsb]][23:16] <= data.WDATA[23:16];
              end
              if (data.WSTRB[3]) begin
                mem_array[data.AWADDR[AddrMsb:AddrLsb]][31:24] <= data.WDATA[31:24];
              end
              data.BRESP <= ResponseOkay;
              data.BVALID <= 1'b1;
            end else begin
                data.BVALID <= 1'b0;
            end
        end
    end

endmodule

/** This is used for testing MemoryAxiLite in simulation, since Verilator doesn't allow
SV interfaces in top-level modules. We expose all of the AXIL signals here so that tests
can interact with them. */
module MemAxiLiteTester #(
    parameter int NUM_WORDS  = 32,
    parameter int ADDR_WIDTH = 32,
    parameter int DATA_WIDTH = 32
) (
    input wire ACLK,
    input wire ARESETn,

    input  wire                   I_ARVALID,
    output logic                  I_ARREADY,
    input  wire  [ADDR_WIDTH-1:0] I_ARADDR,
    input  wire  [           2:0] I_ARPROT,
    output logic                  I_RVALID,
    input  wire                   I_RREADY,
    output logic [ADDR_WIDTH-1:0] I_RDATA,
    output logic [           1:0] I_RRESP,

    input  wire                       I_AWVALID,
    output logic                      I_AWREADY,
    input  wire  [    ADDR_WIDTH-1:0] I_AWADDR,
    input  wire  [               2:0] I_AWPROT,
    input  wire                       I_WVALID,
    output logic                      I_WREADY,
    input  wire  [    DATA_WIDTH-1:0] I_WDATA,
    input  wire  [(DATA_WIDTH/8)-1:0] I_WSTRB,
    output logic                      I_BVALID,
    input  wire                       I_BREADY,
    output logic [               1:0] I_BRESP,

    input  wire                   D_ARVALID,
    output logic                  D_ARREADY,
    input  wire  [ADDR_WIDTH-1:0] D_ARADDR,
    input  wire  [           2:0] D_ARPROT,
    output logic                  D_RVALID,
    input  wire                   D_RREADY,
    output logic [ADDR_WIDTH-1:0] D_RDATA,
    output logic [           1:0] D_RRESP,

    input  wire                       D_AWVALID,
    output logic                      D_AWREADY,
    input  wire  [    ADDR_WIDTH-1:0] D_AWADDR,
    input  wire  [               2:0] D_AWPROT,
    input  wire                       D_WVALID,
    output logic                      D_WREADY,
    input  wire  [    DATA_WIDTH-1:0] D_WDATA,
    input  wire  [(DATA_WIDTH/8)-1:0] D_WSTRB,
    output logic                      D_BVALID,
    input  wire                       D_BREADY,
    output logic [               1:0] D_BRESP
);

  axi_clkrst_if axi (.*);
  axi_if #(
      .ADDR_WIDTH(ADDR_WIDTH),
      .DATA_WIDTH(DATA_WIDTH)
  ) insn ();
  assign insn.manager.ARVALID = I_ARVALID;
  assign I_ARREADY = insn.manager.ARREADY;
  assign insn.manager.ARADDR = I_ARADDR;
  assign insn.manager.ARPROT = I_ARPROT;
  assign I_RVALID = insn.manager.RVALID;
  assign insn.manager.RREADY = I_RREADY;
  assign I_RRESP = insn.manager.RRESP;
  assign I_RDATA = insn.manager.RDATA;

  axi_if #(
      .ADDR_WIDTH(ADDR_WIDTH),
      .DATA_WIDTH(DATA_WIDTH)
  ) data ();
  assign data.manager.ARVALID = D_ARVALID;
  assign D_ARREADY = data.manager.ARREADY;
  assign data.manager.ARADDR = D_ARADDR;
  assign data.manager.ARPROT = D_ARPROT;
  assign D_RVALID = data.manager.RVALID;
  assign data.manager.RREADY = D_RREADY;
  assign D_RRESP = data.manager.RRESP;
  assign D_RDATA = data.manager.RDATA;

  assign data.manager.AWVALID = D_AWVALID;
  assign D_AWREADY = data.manager.AWREADY;
  assign data.manager.AWADDR = D_AWADDR;
  assign data.manager.AWPROT = D_AWPROT;
  assign data.manager.WVALID = D_WVALID;
  assign D_WREADY = data.manager.WREADY;
  assign data.manager.WDATA = D_WDATA;
  assign data.manager.WSTRB = D_WSTRB;
  assign D_BVALID = data.manager.BVALID;
  assign data.manager.BREADY = D_BREADY;
  assign D_BRESP = data.manager.BRESP;

  MemoryAxiLite #(
      .NUM_WORDS(NUM_WORDS)
  ) mem (
      .axi (axi),
      .insn(insn.subord),
      .data(data.subord)
  );
endmodule

/**
 * This enum is used to classify each cycle as it comes through the Writeback stage, identifying
 * if a valid insn is present or, if it is a stall cycle instead, the reason for the stall. The
 * enum values are mutually exclusive: only one should be set for any given cycle. These values
 * are compared against the trace-*.json files to ensure that the datapath is running with the
 * correct timing.
 *
 * You will need to set these values at various places within your pipeline, and propagate them
 * through the stages until they reach Writeback where they can be checked.
 */
typedef enum {
  /** invalid value, this should never appear after the initial reset sequence completes */
  CYCLE_INVALID = 0,
  /** a stall cycle that arose from the initial reset signal */
  CYCLE_RESET = 1,
  /** not a stall cycle, a valid insn is in Writeback */
  CYCLE_NO_STALL = 2,
  /** a stall cycle that arose from a taken branch/jump */
  CYCLE_TAKEN_BRANCH = 4,
  /** a stall cycle that arose from a load-to-use stall */
  CYCLE_LOAD2USE = 8,
  /** a stall cycle that arose from a div/rem-to-use stall */
  CYCLE_DIV2USE = 16,
  /** a stall cycle that arose from a fence insn */
  CYCLE_FENCEI = 32
} cycle_status_e;

/** state at the start of Decode stage */
typedef struct packed {
  logic [`REG_SIZE] pc;
  logic [`INSN_SIZE] insn;
  cycle_status_e cycle_status;
  logic [`REG_SIZE] curr_cy;

} stage_decode_t;

typedef struct packed {
  logic [`REG_SIZE] pc;
  logic [`REG_SIZE] a;
  logic [`REG_SIZE] b;
  logic [`INSN_SIZE] insn;
  cycle_status_e cycle_status;
  logic [`REG_SIZE] curr_cy;
} stage_execute_t;

typedef struct packed {
  logic [`REG_SIZE] pc;
  logic [`REG_SIZE] o;
  logic [`REG_SIZE] b;
  logic [`INSN_SIZE] insn;
  logic we;
  logic [3:0] data_we;
  logic illegal_insn;
  cycle_status_e cycle_status;
  logic [`REG_SIZE] mba;
  logic [`REG_SIZE] mbb;
  logic [`REG_SIZE] mso;
  logic [`REG_SIZE] wmw;
  logic [`REG_SIZE] esa;
  logic [`REG_SIZE] curr_cy;
  logic [`REG_SIZE] to_mem;

} stage_memory_t;

typedef struct packed {
  logic [`REG_SIZE] pc;
  logic [`REG_SIZE] o;
  logic [`REG_SIZE] d;
  logic [`INSN_SIZE] insn;
  logic we;
  logic [`REG_SIZE] div_res;
  logic illegal_insn;
  cycle_status_e cycle_status;
  logic [`REG_SIZE] curr_cy;
  logic [4:0] insn_rd;
} stage_writeback_t;

module DatapathAxilMemory (
    input wire clk,
    input wire rst,

    // Start by replacing this interface to imem...
    //output logic [`REG_SIZE] pc_to_imem,
    //input wire [`INSN_SIZE] insn_from_imem,
    // ...with this AXIL one.
    axi_if.manager imem,

    // Once imem is working, replace this interface to dmem...
    //output logic [`REG_SIZE] addr_to_dmem,
    //input wire [`REG_SIZE] load_data_from_dmem,
    //output logic [`REG_SIZE] store_data_to_dmem,
    //output logic [3:0] store_we_to_dmem,
    // ...with this AXIL one
    axi_if.manager dmem,

    output logic halt,

    // The PC of the insn currently in Writeback. 0 if not a valid insn.
    output logic [`REG_SIZE] trace_writeback_pc,
    // The bits of the insn currently in Writeback. 0 if not a valid insn.
    output logic [`INSN_SIZE] trace_writeback_insn,
    // The status of the insn (or stall) currently in Writeback. See cycle_status_e enum for valid values.
    output cycle_status_e trace_writeback_cycle_status
);

  // TODO: your code here

  // opcodes - see section 19 of RiscV spec
  localparam bit [`OPCODE_SIZE] OpcodeLoad = 7'b00_000_11;
  localparam bit [`OPCODE_SIZE] OpcodeStore = 7'b01_000_11;
  localparam bit [`OPCODE_SIZE] OpcodeBranch = 7'b11_000_11;
  localparam bit [`OPCODE_SIZE] OpcodeJalr = 7'b11_001_11;
  localparam bit [`OPCODE_SIZE] OpcodeMiscMem = 7'b00_011_11;
  localparam bit [`OPCODE_SIZE] OpcodeJal = 7'b11_011_11;

  localparam bit [`OPCODE_SIZE] OpcodeRegImm = 7'b00_100_11;
  localparam bit [`OPCODE_SIZE] OpcodeRegReg = 7'b01_100_11;
  localparam bit [`OPCODE_SIZE] OpcodeEnviron = 7'b11_100_11;

  localparam bit [`OPCODE_SIZE] OpcodeAuipc = 7'b00_101_11;
  localparam bit [`OPCODE_SIZE] OpcodeLui = 7'b01_101_11;

  // cycle counter, not really part of any stage but useful for orienting within GtkWave
  // do not rename this as the testbench uses this value
  logic [`REG_SIZE] cycles_current;
  always_ff @(posedge clk) begin
    if (rst) begin
      cycles_current <= 0;
    end else begin
      cycles_current <= cycles_current + 1;
    end
  end

  /***************/
  /* FETCH STAGE */
  /***************/

  logic [`REG_SIZE] f_pc_current;
  logic [`REG_SIZE] f_insn;
  cycle_status_e f_cycle_status;

  logic fd_clear_for_branch;  // this is used when we clear the whole thing for branch
  logic [`REG_SIZE] fd_new_pc;  //set when we branch

  logic stall_for_load;
  logic stall_for_fence;
  logic stall_for_div;

  // program counter
  always_ff @(posedge clk) begin
    if (rst) begin
      f_pc_current   <= 32'd0;
      // NB: use CYCLE_NO_STALL since this is the value that will persist after the last reset cycle
      f_cycle_status <= CYCLE_NO_STALL;
      
    end else begin
      f_cycle_status <= CYCLE_NO_STALL;

      if (fd_clear_for_branch) begin
        f_pc_current <= fd_new_pc;  // Jump to new PC on branch
      end else if (stall_for_load || stall_for_fence || stall_for_div) begin
        f_pc_current <= f_pc_current;  
      end else begin
        f_pc_current <= f_pc_current + 4;
      end



    end
  end
  

 always_comb begin
      imem.ARADDR = f_pc_current;  
      if (rst) begin
        imem.ARVALID = 1'b0;
      end else begin
    
        imem.ARVALID = 1'b1; 

        if (stall_for_load || stall_for_fence || stall_for_div) begin
            imem.ARVALID = 1'b0;        
        end
      end

 end 



 


  // Here's how to disassemble an insn into a string you can view in GtkWave.
  // Use PREFIX to provide a 1-character tag to identify which stage the insn comes from.
  wire [255:0] f_disasm;
  Disasm #(
      .PREFIX("F")
  ) disasm_0fetch (
      .insn  (f_insn),
      .disasm(f_disasm)
  );

  /****************/
  /* DECODE STAGE */
  /****************/

  // this shows how to package up state in a `struct packed`, and how to pass it between stages
  logic prev_stall;
  logic prev_branch;
  logic [`REG_SIZE] prev_insn;
  stage_decode_t decode_state;

  always_comb begin
    if (prev_stall) begin
      assign f_insn = prev_insn;
    end else 
    if (prev_branch) begin
      assign f_insn = 32'b0;
    end else begin
      assign f_insn = imem.RVALID ? imem.RDATA : 32'b0;
    end 

  end


  assign prev_insn = imem.RDATA;

  always_ff @(posedge clk) begin
    if (rst) begin
      decode_state <= '{pc: 0, insn: 0, cycle_status: CYCLE_RESET, curr_cy: 0};
    end else begin
      if (fd_clear_for_branch) begin
        prev_branch <= 1'b1;
        decode_state <= '{pc: 0, insn: 0, cycle_status: CYCLE_TAKEN_BRANCH, curr_cy: 0};
      end else if (stall_for_load || stall_for_fence || stall_for_div) begin
        decode_state <= decode_state;
        prev_stall <= 1'b1;
      end else begin
        decode_state <= '{
            pc: f_pc_current,
            insn: f_insn,
            cycle_status: f_cycle_status,
            curr_cy: cycles_current + 1
        };
        prev_stall <= 1'b0;
        prev_branch <= 1'b0;
      end
    end
  end
  wire [255:0] d_disasm;
  Disasm #(
      .PREFIX("D")
  ) disasm_1decode (
      .insn  (f_insn),
      .disasm(d_disasm)
  );

  // TODO: your code here, though you will also need to modify some of the code above
  // TODO: the testbench requires that your register file instance is named `rf`

  always_comb begin
    stall_for_load = 1'b0;
    if (execute_state.insn[6:0] == OpcodeLoad) begin
      if ((f_insn[19:15] == execute_state.insn[11:7] && f_insn[19:15] != 5'd0) ||
          ((f_insn[24:20] == execute_state.insn[11:7] && f_insn[24:20] != 5'd0) &&
          (f_insn[6:0] != OpcodeStore) &&
          (f_insn[6:0] != OpcodeRegImm) &&
          (f_insn[6:0] != OpcodeLoad))) begin
        stall_for_load = 1'b1;
      end
    end
  end

  always_comb begin
    stall_for_fence = 1'b0;
    if (f_insn[6:0] == OpcodeMiscMem 
    && (execute_state.insn[6:0] == OpcodeStore || memory_state.insn[6:0] == OpcodeStore)) begin
      stall_for_fence = 1'b1;
    end
  end

  always_comb begin
    stall_for_div = 1'b0;
    if (execute_state.insn[6:0] == OpcodeRegReg && execute_state.insn[31:25] == 7'd1) begin
      if ((execute_state.insn[11:7] == f_insn[19:15] && f_insn[19:15] != 5'b0)
      || (execute_state.insn[11:7] == f_insn[24:20]&& f_insn[24:20] != 5'b0)) begin
        stall_for_div = 1'b1;
      end
    end
  end


  /*****************/
  /* EXECUTE STAGE */
  /*****************/


  logic [4:0] rf_rd;
  logic [`REG_SIZE] rf_rd_data;
  logic [4:0] rf_rs1;
  logic [`REG_SIZE] rf_rs1_data;
  logic [4:0] rf_rs2;
  logic [`REG_SIZE] rf_rs2_data;

  logic rf_we;

  RegFile rf (
      .rd(rf_rd),
      .rd_data(rf_rd_data),
      .rs1(rf_rs1),
      .rs1_data(rf_rs1_data),
      .rs2(rf_rs2),
      .rs2_data(rf_rs2_data),
      .clk(clk),
      .rst(rst),
      .we(rf_we)
  );

  // breaking down the instruction
  wire [6:0] x_insn_funct7;
  wire [4:0] x_insn_rs2;
  wire [4:0] x_insn_rs1;
  wire [2:0] x_insn_funct3;
  wire [4:0] x_insn_rd;
  wire [`OPCODE_SIZE] x_insn_opcode;

  assign {x_insn_funct7, x_insn_rs2, x_insn_rs1, x_insn_funct3, x_insn_rd, x_insn_opcode} = f_insn;

  // getting our outputs from memory
  logic [`REG_SIZE] x_rs1_data;
  logic [`REG_SIZE] x_rs2_data;

  always_comb begin
    rf_rs1 = x_insn_rs1;
    rf_rs2 = x_insn_rs2;

    //WD bypassing
    if (writeback_state.insn[11:7] == f_insn[19:15] 
        && writeback_state.insn[11:7] != 5'b0
        && (writeback_state.insn[6:0] != OpcodeStore
            && writeback_state.insn[6:0] != OpcodeBranch)
        ) begin
      x_rs1_data = w_mux_writeback;
    end else begin
      x_rs1_data = rf_rs1_data;
    end

    if (writeback_state.insn[11:7] == f_insn[24:20] 
        && writeback_state.insn[11:7] != 5'b0
        && (writeback_state.insn[6:0] != OpcodeStore
            && writeback_state.insn[6:0] != OpcodeBranch)
        && (f_insn[6:0] == OpcodeRegReg 
            || f_insn[6:0] == OpcodeStore 
            || f_insn[6:0] == OpcodeBranch)
        ) begin
      x_rs2_data = w_mux_writeback;
    end else begin
      x_rs2_data = rf_rs2_data;
    end

  end

  stage_execute_t execute_state;
  always_ff @(posedge clk) begin
    if (rst) begin
      execute_state <= '{pc: 0, insn: 0, a: 0, b: 0, cycle_status: CYCLE_RESET, curr_cy: 0};
    end else begin
      begin
        if (fd_clear_for_branch) begin
          execute_state <= '{
              pc: 0,
              a: 0,
              b: 0,
              insn: 0,
              cycle_status: CYCLE_TAKEN_BRANCH,
              curr_cy: 0
          };
        end else if (stall_for_load) begin
          execute_state <= '{
              pc: 0,
              a: 0,
              b: 0,
              insn: 0,
              cycle_status: CYCLE_LOAD2USE,
              curr_cy: 0
          };
        end else if (stall_for_fence) begin
          execute_state <= '{
              pc: 0,
              a: 0,
              b: 0,
              insn: 0,
              cycle_status: CYCLE_FENCEI,
              curr_cy: 0
          };
        end else if (stall_for_div) begin
          execute_state <= '{
              pc: 0,
              a: 0,
              b: 0,
              insn: 0,
              cycle_status: CYCLE_DIV2USE,
              curr_cy: 0
          };
        end else begin
          execute_state <= '{
              pc: decode_state.pc,
              a: x_rs1_data,
              b: x_rs2_data,
              insn: f_insn,
              cycle_status: decode_state.cycle_status,
              curr_cy: decode_state.curr_cy
          };
        end
      end
    end
  end
  wire [255:0] x_disasm;
  Disasm #(
      .PREFIX("X")
  ) disasm_1execute (
      .insn  (execute_state.insn),
      .disasm(x_disasm)
  );


  /*****************/
  /* MEMORY STAGE */
  /*****************/
  logic [`OPCODE_SIZE] m_insn_opcode;
  assign m_insn_opcode = execute_state.insn[6:0];

  wire insn_lui = m_insn_opcode == OpcodeLui;
  wire insn_auipc = m_insn_opcode == OpcodeAuipc;
  wire insn_jal = m_insn_opcode == OpcodeJal;
  wire insn_jalr = m_insn_opcode == OpcodeJalr;

  wire insn_beq = m_insn_opcode == OpcodeBranch && execute_state.insn[14:12] == 3'b000;
  wire insn_bne = m_insn_opcode == OpcodeBranch && execute_state.insn[14:12] == 3'b001;
  wire insn_blt = m_insn_opcode == OpcodeBranch && execute_state.insn[14:12] == 3'b100;
  wire insn_bge = m_insn_opcode == OpcodeBranch && execute_state.insn[14:12] == 3'b101;
  wire insn_bltu = m_insn_opcode == OpcodeBranch && execute_state.insn[14:12] == 3'b110;
  wire insn_bgeu = m_insn_opcode == OpcodeBranch && execute_state.insn[14:12] == 3'b111;

  wire insn_lb = m_insn_opcode == OpcodeLoad && execute_state.insn[14:12] == 3'b000;
  wire insn_lh = m_insn_opcode == OpcodeLoad && execute_state.insn[14:12] == 3'b001;
  wire insn_lw = m_insn_opcode == OpcodeLoad && execute_state.insn[14:12] == 3'b010;
  wire insn_lbu = m_insn_opcode == OpcodeLoad && execute_state.insn[14:12] == 3'b100;
  wire insn_lhu = m_insn_opcode == OpcodeLoad && execute_state.insn[14:12] == 3'b101;

  wire insn_sb = m_insn_opcode == OpcodeStore && execute_state.insn[14:12] == 3'b000;
  wire insn_sh = m_insn_opcode == OpcodeStore && execute_state.insn[14:12] == 3'b001;
  wire insn_sw = m_insn_opcode == OpcodeStore && execute_state.insn[14:12] == 3'b010;

  wire insn_addi = m_insn_opcode == OpcodeRegImm && execute_state.insn[14:12] == 3'b000;
  wire insn_slti = m_insn_opcode == OpcodeRegImm && execute_state.insn[14:12] == 3'b010;
  wire insn_sltiu = m_insn_opcode == OpcodeRegImm && execute_state.insn[14:12] == 3'b011;
  wire insn_xori = m_insn_opcode == OpcodeRegImm && execute_state.insn[14:12] == 3'b100;
  wire insn_ori = m_insn_opcode == OpcodeRegImm && execute_state.insn[14:12] == 3'b110;
  wire insn_andi = m_insn_opcode == OpcodeRegImm && execute_state.insn[14:12] == 3'b111;

  wire insn_slli = m_insn_opcode == OpcodeRegImm && execute_state.insn[14:12] == 3'b001 && execute_state.insn[31:25] == 7'd0;
  wire insn_srli = m_insn_opcode == OpcodeRegImm && execute_state.insn[14:12] == 3'b101 && execute_state.insn[31:25] == 7'd0;
  wire insn_srai = m_insn_opcode == OpcodeRegImm && execute_state.insn[14:12] == 3'b101 && execute_state.insn[31:25] == 7'b0100000;

  wire insn_add = m_insn_opcode == OpcodeRegReg && execute_state.insn[14:12] == 3'b000 && execute_state.insn[31:25] == 7'd0;
  wire insn_sub  = m_insn_opcode == OpcodeRegReg && execute_state.insn[14:12] == 3'b000 && execute_state.insn[31:25] == 7'b0100000;
  wire insn_sll = m_insn_opcode == OpcodeRegReg && execute_state.insn[14:12] == 3'b001 && execute_state.insn[31:25] == 7'd0;
  wire insn_slt = m_insn_opcode == OpcodeRegReg && execute_state.insn[14:12] == 3'b010 && execute_state.insn[31:25] == 7'd0;
  wire insn_sltu = m_insn_opcode == OpcodeRegReg && execute_state.insn[14:12] == 3'b011 && execute_state.insn[31:25] == 7'd0;
  wire insn_xor = m_insn_opcode == OpcodeRegReg && execute_state.insn[14:12] == 3'b100 && execute_state.insn[31:25] == 7'd0;
  wire insn_srl = m_insn_opcode == OpcodeRegReg && execute_state.insn[14:12] == 3'b101 && execute_state.insn[31:25] == 7'd0;
  wire insn_sra  = m_insn_opcode == OpcodeRegReg && execute_state.insn[14:12] == 3'b101 && execute_state.insn[31:25] == 7'b0100000;
  wire insn_or = m_insn_opcode == OpcodeRegReg && execute_state.insn[14:12] == 3'b110 && execute_state.insn[31:25] == 7'd0;
  wire insn_and = m_insn_opcode == OpcodeRegReg && execute_state.insn[14:12] == 3'b111 && execute_state.insn[31:25] == 7'd0;

  wire insn_mul    = m_insn_opcode == OpcodeRegReg && execute_state.insn[31:25] == 7'd1 && execute_state.insn[14:12] == 3'b000;
  wire insn_mulh   = m_insn_opcode == OpcodeRegReg && execute_state.insn[31:25] == 7'd1 && execute_state.insn[14:12] == 3'b001;
  wire insn_mulhsu = m_insn_opcode == OpcodeRegReg && execute_state.insn[31:25] == 7'd1 && execute_state.insn[14:12] == 3'b010;
  wire insn_mulhu  = m_insn_opcode == OpcodeRegReg && execute_state.insn[31:25] == 7'd1 && execute_state.insn[14:12] == 3'b011;
  wire insn_div    = m_insn_opcode == OpcodeRegReg && execute_state.insn[31:25] == 7'd1 && execute_state.insn[14:12] == 3'b100;
  wire insn_divu   = m_insn_opcode == OpcodeRegReg && execute_state.insn[31:25] == 7'd1 && execute_state.insn[14:12] == 3'b101;
  wire insn_rem    = m_insn_opcode == OpcodeRegReg && execute_state.insn[31:25] == 7'd1 && execute_state.insn[14:12] == 3'b110;
  wire insn_remu   = m_insn_opcode == OpcodeRegReg && execute_state.insn[31:25] == 7'd1 && execute_state.insn[14:12] == 3'b111;

  wire insn_ecall = m_insn_opcode == OpcodeEnviron && execute_state.insn[31:7] == 25'd0;
  wire insn_fence = m_insn_opcode == OpcodeMiscMem;


  logic [31:0] cla_a;
  logic [31:0] cla_b;
  logic cla_cin;
  logic [31:0] cla_sum;

  cla cla_inst (
      .a  (cla_a),
      .b  (cla_b),
      .cin(cla_cin),
      .sum(cla_sum)
  );

  logic [`REG_SIZE] dividend, divisor, remainder, quotient;

  divider_unsigned_pipelined divider_inst (
      .clk(clk),
      .rst(rst),
      .i_dividend(dividend),
      .i_divisor(divisor),
      .o_quotient(quotient),
      .o_remainder(remainder)
  );

  //calculating the output
  logic [`REG_SIZE] m_output;
  logic illegal_insn;

  wire [6:0] m_insn_funct7;
  assign m_insn_funct7 = execute_state.insn[31:25];

  wire [4:0] m_insn_rd;
  assign m_insn_rd = execute_state.insn[11:7];

  //this block right here is kind of our ALU if you think about it
  wire [11:0] imm_i;
  assign imm_i = execute_state.insn[31:20];
  wire [ 4:0] imm_shamt = execute_state.insn[24:20];
  wire [31:0] imm_i_sext = {{20{imm_i[11]}}, imm_i};

  wire [12:0] imm_b;
  assign {imm_b[12], imm_b[10:5]} = m_insn_funct7,
      {imm_b[4:1], imm_b[11]} = m_insn_rd,
      imm_b[0] = 1'b0;
  wire [`REG_SIZE] imm_b_sext = {{19{imm_b[12]}}, imm_b[12:0]};

  wire [20:0] imm_j;
  assign {imm_j[20], imm_j[10:1], imm_j[11], imm_j[19:12], imm_j[0]} = {
    execute_state.insn[31:12], 1'b0
  };
  wire [`REG_SIZE] imm_j_sext = {{11{imm_j[20]}}, imm_j[20:0]};

  wire [11:0] imm_s;
  assign imm_s[11:5] = execute_state.insn[31:25], imm_s[4:0] = execute_state.insn[11:7];
  wire  [`REG_SIZE] imm_s_sext = {{20{imm_s[11]}}, imm_s[11:0]};


  logic [`REG_SIZE] m_bypass_a;
  logic [`REG_SIZE] m_bypass_b;

  logic [63:0] mul_h, mul_hsu, mul_hu;

  logic m_we;

  logic [3:0] m_data_we;



  always_comb begin
    // WX/MX BYPASSING
    if (memory_state.insn[11:7] == execute_state.insn[19:15] 
        && memory_state.insn[11:7] != 5'b0
        && memory_state.insn[6:0] != OpcodeStore
        && memory_state.insn[6:0] != OpcodeBranch
        && memory_state.insn[6:0] !=  0'b1110011
        && memory_state.we) begin
      m_bypass_a = memory_state.o;
    end else if (writeback_state.insn[11:7] == execute_state.insn[19:15] 
        && writeback_state.insn[11:7] != 5'b0
        && writeback_state.insn[6:0] != OpcodeStore
        && writeback_state.insn[6:0] != OpcodeBranch
        && writeback_state.insn[6:0] !=  0'b1110011
        && writeback_state.we) begin
      m_bypass_a = w_mux_writeback;
    end else begin
      m_bypass_a = execute_state.a;
    end

    if (memory_state.insn[11:7] == execute_state.insn[24:20] 
        && memory_state.insn[11:7] != 5'b0
        && memory_state.insn[6:0] != OpcodeStore
        && memory_state.insn[6:0] != OpcodeBranch
        && memory_state.insn[6:0] !=  0'b1110011
        && memory_state.we
        && (
          execute_state.insn[6:0] == OpcodeRegReg
          || execute_state.insn[6:0] == OpcodeStore
          || execute_state.insn[6:0] == OpcodeBranch)) begin
      m_bypass_b = memory_state.o;
    end else if (writeback_state.insn[11:7] == execute_state.insn[24:20] 
        && writeback_state.insn[11:7] != 5'b0
        && writeback_state.insn[6:0] != OpcodeStore
        && writeback_state.insn[6:0] != OpcodeBranch
        && writeback_state.insn[6:0] !=  0'b1110011
        && writeback_state.we
        && (
          execute_state.insn[6:0] == OpcodeRegReg
          || execute_state.insn[6:0] == OpcodeStore
          || execute_state.insn[6:0] == OpcodeBranch
        )) begin
      m_bypass_b = w_mux_writeback;
    end else begin
      m_bypass_b = execute_state.b;
    end


  end

  logic [`REG_SIZE] x_addr_to_mem;

  always_comb begin

    // halt = 1'b0;

    illegal_insn = 1'b0;
    cla_a = 32'd0;
    cla_b = 32'd0;
    cla_cin = 1'b0;

    m_output = 32'd0;

    fd_new_pc = 32'd0;
    fd_clear_for_branch = 1'b0;

    mul_h = 64'd0;
    mul_hsu = 64'd0;
    mul_hu = 64'd0;

    dividend = 32'd0;
    divisor = 32'd0;

    m_we = 1'b0;
    m_data_we = 4'b0;

    x_addr_to_mem = 32'd0;

    // stall_for_load = 1'b0;


    // stall_for_fence = 1'b0;

    case (m_insn_opcode)
      OpcodeLui: begin
        m_output = {execute_state.insn[31:12], 12'd0};
        m_we = 1'b1;
      end
      OpcodeRegImm: begin
        m_we = 1'b1;
        if (insn_addi) begin
          cla_a = m_bypass_a;
          cla_b = imm_i_sext;
          cla_cin = 1'b0;
          m_output = cla_sum;
        end else if (insn_slti) begin
          if ($signed(m_bypass_a) < $signed(imm_i_sext)) begin
            m_output = 32'b1;
          end else begin
            m_output = 32'b0;
          end
        end else if (insn_sltiu) begin
          if (m_bypass_a < imm_i_sext) begin
            m_output = 32'b1;
          end else begin
            m_output = 32'b0;
          end
        end else if (insn_xori) begin
          m_output = m_bypass_a ^ imm_i_sext;
        end else if (insn_ori) begin
          m_output = m_bypass_a | imm_i_sext;
        end else if (insn_andi) begin
          m_output = m_bypass_a & imm_i_sext;
        end else if (insn_slli) begin
          m_output = m_bypass_a << imm_shamt;
        end else if (insn_srli) begin
          m_output = m_bypass_a >> imm_shamt;
        end else if (insn_srai) begin
          m_output = $signed(m_bypass_a) >>> imm_shamt;
        end else begin
          m_we = 1'b0;
          illegal_insn = 1'b1;
        end
      end
      OpcodeRegReg: begin
        m_we = 1'b1;
        if (insn_add) begin
          cla_a = m_bypass_a;
          cla_b = m_bypass_b;
          cla_cin = 1'b0;
          m_output = cla_sum;
        end else if (insn_sub) begin
          cla_a = m_bypass_a;
          cla_b = ~m_bypass_b;
          cla_cin = 1'b1;
          m_output = cla_sum;
        end else if (insn_sll) begin
          m_output = m_bypass_a << (m_bypass_b[4:0]);
        end else if (insn_slt) begin
          if (signed'(m_bypass_a) < signed'(m_bypass_b)) begin
            m_output = 32'b1;
          end else begin
            m_output = 32'b0;
          end
        end else if (insn_sltu) begin
          if (m_bypass_a < m_bypass_b) begin
            m_output = 32'b1;
          end else begin
            m_output = 32'b0;
          end
        end else if (insn_xor) begin
          m_output = m_bypass_a ^ m_bypass_b;
        end else if (insn_srl) begin
          m_output = m_bypass_a >> m_bypass_b[4:0];
        end else if (insn_sra) begin
          m_output = $signed(m_bypass_a) >>> m_bypass_b[4:0];
        end else if (insn_or) begin
          m_output = m_bypass_a | m_bypass_b;
        end else if (insn_and) begin
          m_output = m_bypass_a & m_bypass_b;
        end else if (insn_mul) begin
          m_output = m_bypass_a * m_bypass_b;
        end else if (insn_mulh) begin
          mul_h = {{32{m_bypass_a[31]}}, m_bypass_a} * {{32{m_bypass_b[31]}}, m_bypass_b};
          m_output = mul_h[63:32];
        end else if (insn_mulhsu) begin
          mul_hsu  = {{32{m_bypass_a[31]}}, m_bypass_a} * {32'b0, m_bypass_b};
          m_output = mul_hsu[63:32];
        end else if (insn_mulhu) begin
          mul_hu   = m_bypass_a * m_bypass_b;
          m_output = mul_hu[63:32];
        end else if (insn_div) begin
          if (m_bypass_a[31]) begin
            dividend = ~m_bypass_a + 1;
          end else begin
            dividend = m_bypass_a;
          end
          if (m_bypass_b[31]) begin
            divisor = ~m_bypass_b + 1;
          end else begin
            divisor = m_bypass_b;
          end
          if (!(m_bypass_a[31] ^ m_bypass_b[31]) || (m_bypass_b == 'd0)) begin
            m_output = 32'b1;
          end else begin
            m_output = 32'b0;
          end
        end else if (insn_divu) begin
          dividend = m_bypass_a;
          divisor  = m_bypass_b;
          m_output = 32'b1;
        end else if (insn_rem) begin
          if (m_bypass_a[31]) begin
            dividend = ~m_bypass_a + 1;
          end else begin
            dividend = m_bypass_a;
          end
          if (m_bypass_b[31]) begin
            divisor = ~m_bypass_b + 1;
          end else begin
            divisor = m_bypass_b;
          end
          if (m_bypass_a[31]) begin
            m_output = 32'b1;
          end else begin
            m_output = 32'b0;
          end
        end else if (insn_remu) begin
          dividend = m_bypass_a;
          divisor  = m_bypass_b;
          m_output = 32'b1;
        end else begin
          m_we = 1'b0;
          illegal_insn = 1'b1;
        end
      end
      OpcodeLoad: begin
        m_we = 1'b1;

        if (insn_lb || insn_lh || insn_lw || insn_lbu || insn_lhu) begin
          m_output = m_bypass_a + imm_i_sext;
          x_addr_to_mem = m_bypass_a + imm_i_sext;
        end
      end
      OpcodeJal: begin
        m_we = 1'b1;
        if (insn_jal) begin
          fd_new_pc = execute_state.pc + imm_j_sext;
          fd_clear_for_branch = 1'b1;
          m_output = execute_state.pc + 4;
        end else begin
          illegal_insn = 1'b1;
        end
      end
      OpcodeJalr: begin
        m_we = 1'b1;
        if (insn_jalr) begin
          fd_new_pc = (m_bypass_a + imm_i_sext) & ~(32'h1);
          fd_clear_for_branch = 1'b1;
          m_output = execute_state.pc + 4;
        end else begin
          illegal_insn = 1'b1;
        end
      end
      OpcodeBranch: begin
        m_we = 1'b0;
        if (insn_beq) begin
          if (m_bypass_a == m_bypass_b) begin
            fd_new_pc = execute_state.pc + imm_b_sext;
            fd_clear_for_branch = 1'b1;
          end
        end else if (insn_bne) begin
          if (m_bypass_a != m_bypass_b) begin
            fd_new_pc = execute_state.pc + imm_b_sext;
            fd_clear_for_branch = 1'b1;
          end
        end else if (insn_blt) begin
          if (signed'(m_bypass_a) < signed'(m_bypass_b)) begin
            fd_new_pc = execute_state.pc + imm_b_sext;
            fd_clear_for_branch = 1'b1;
          end
        end else if (insn_bge) begin
          if (signed'(m_bypass_a) >= signed'(m_bypass_b)) begin
            fd_new_pc = execute_state.pc + imm_b_sext;
            fd_clear_for_branch = 1'b1;
          end
        end else if (insn_bltu) begin
          if (m_bypass_a < m_bypass_b) begin
            fd_new_pc = execute_state.pc + imm_b_sext;
            fd_clear_for_branch = 1'b1;
          end
        end else if (insn_bgeu) begin
          if (m_bypass_a >= m_bypass_b) begin
            fd_new_pc = execute_state.pc + imm_b_sext;
            fd_clear_for_branch = 1'b1;
          end
        end else begin
          illegal_insn = 1'b1;
        end
      end
      OpcodeEnviron: begin
        m_we = 1'b0;
        if (insn_ecall) begin
          // halt = 1'b1
          // this is handled down the line
        end else begin
          illegal_insn = 1'b1;
        end
      end
      OpcodeAuipc: begin
        m_we = 1'b0;
        if (insn_auipc) begin
          m_output = execute_state.pc + {execute_state.insn[31:12], 12'd0};
          m_we = 1'b1;
        end else begin
          illegal_insn = 1'b1;
        end
      end
      OpcodeStore: begin
        m_output = m_bypass_a + imm_s_sext;
        x_addr_to_mem = m_bypass_a + imm_s_sext;
        if (insn_sb) begin
          case (m_output[1:0])
            2'b00: begin
              m_data_we = 4'b0001;
            end
            2'b01: begin
              m_data_we = 4'b0010;
            end
            2'b10: begin
              m_data_we = 4'b0100;
            end
            2'b11: begin
              m_data_we = 4'b1000;
            end
          endcase
        end else if (insn_sh) begin
          m_data_we = 4'b0011;
          case (m_output[1])
            1'b0: begin
              m_data_we = 4'b0011;
            end
            1'b1: begin
              m_data_we = 4'b1100;
            end
          endcase
        end else if (insn_sw) begin
          m_data_we = 4'b1111;
        end else begin
          illegal_insn = 1'b1;
        end
      end
      OpcodeMiscMem: begin
        // if (insn_fence) begin
        //   if (memory_state.insn[6:0] == OpcodeStore) begin
        //     stall_for_fence = 1'b1;
        //   end
        // end else begin
        //   illegal_insn = 1'b1;
        // end
      end
      default: begin
        m_we = 1'b0;
        illegal_insn = 1'b1;
      end
    endcase
  end



  stage_memory_t memory_state;
  always_ff @(posedge clk) begin
    if (rst) begin
      memory_state <= '{
          pc: 0,
          insn: 0,
          o: 0,
          b: 0,
          we: 0,
          data_we: 0,
          illegal_insn: 0,
          cycle_status: CYCLE_RESET,
          mba: 0,
          mbb: 0,
          mso: 0,
          wmw: 0,
          esa: 0,
          curr_cy: 0,
          to_mem: 0
      };
    end else begin
      begin
        memory_state <= '{
            o: m_output,
            pc: execute_state.pc,
            insn: execute_state.insn,
            // b: execute_state.b,
            b:
            m_bypass_b,
            we: m_we,
            data_we: m_data_we,
            illegal_insn: illegal_insn,
            cycle_status: execute_state.cycle_status,
            mba: m_bypass_a,
            mbb: m_bypass_b,
            mso: memory_state.o,
            wmw: w_mux_writeback,
            esa: execute_state.a,
            curr_cy: execute_state.curr_cy,
            to_mem: x_addr_to_mem
        };
      end
    end
  end
  wire [255:0] m_disasm;
  Disasm #(
      .PREFIX("M")
  ) disasm_1memory (
      .insn  (memory_state.insn),
      .disasm(m_disasm)
  );

  /*****************/
  /* WRITEBACK STAGE */
  /*****************/

  logic [`REG_SIZE] w_loaded_data;
  logic [`REG_SIZE] addr_ld;


  assign addr_ld = memory_state.to_mem;
  assign dmem.ARADDR = {addr_ld[31:2], 2'b00};  
  //assign dmem.ARVALID = (memory_state.insn[6:0] == OpcodeLoad);   
  assign dmem.ARVALID = 1'b1;

  //assign w_loaded_data = load_data_from_dmem[31:0];


  logic [`REG_SIZE] w_bypass_mux_WM;


  always_comb begin
    w_bypass_mux_WM = memory_state.b;
    if (writeback_state.we) begin
      if (writeback_state.insn[11:7] == memory_state.insn[24:20] 
          && (writeback_state.insn[11:7] != 5'b0)) begin
        w_bypass_mux_WM = w_mux_writeback;
      end
    end
  end

  always_comb begin
    dmem.AWADDR = {addr_ld[31:2], 2'b00};  
    dmem.AWVALID = (memory_state.insn[6:0] == OpcodeStore);  
    dmem.WVALID = (memory_state.data_we != 4'b0);  
    dmem.WSTRB = memory_state.data_we;  

      dmem.WDATA = 32'b0;
      case (memory_state.data_we)
        4'b0001: begin
          dmem.WDATA[7:0] = w_bypass_mux_WM[7:0];
        end
        4'b0010: begin
          dmem.WDATA[15:8] = w_bypass_mux_WM[7:0];
        end
        4'b0100: begin
          dmem.WDATA[23:16] = w_bypass_mux_WM[7:0];
        end
        4'b1000: begin
          dmem.WDATA[31:24] = w_bypass_mux_WM[7:0];
        end
        4'b0011: begin
          dmem.WDATA[15:0] = w_bypass_mux_WM[15:0];
        end
        4'b1100: begin
          dmem.WDATA[31:16] = w_bypass_mux_WM[15:0];
        end
        4'b1111: begin
          dmem.WDATA = w_bypass_mux_WM;
        end
        default: begin
          dmem.WDATA = 32'b0;
        end
      endcase

  end

  logic [`REG_SIZE] w_divres;

  always_comb begin
    w_divres = 0;
    if (memory_state.insn[14:12] == 3'b100) begin
      if (memory_state.o == 1) begin
        w_divres = quotient;
      end else begin
        w_divres = ~(quotient) + 'd1;
      end
    end else if (memory_state.insn[14:12] == 3'b101) begin
      w_divres = quotient;
    end else if (memory_state.insn[14:12] == 3'b110) begin
      if (memory_state.o == 1) begin
        w_divres = ~(remainder) + 'd1;
      end else begin
        w_divres = remainder;
      end
    end else if (memory_state.insn[14:12] == 3'b111) begin
      w_divres = remainder;
    end
  end

  stage_writeback_t writeback_state;

  always_comb begin
    w_loaded_data = 32'b0;
    if (dmem.RVALID) begin
        w_loaded_data = dmem.RDATA;  
    end
  end

  always_ff @(posedge clk) begin
    if (rst) begin
      writeback_state <= '{
          pc: 0,
          insn: 0,
          o: 0,
          d: 0,
          we: 0,
          div_res: 0,
          illegal_insn: 0,
          cycle_status: CYCLE_RESET,
          curr_cy: 0,
          insn_rd: 0
      };
    end else begin
      begin
        writeback_state <= '{
            pc: memory_state.pc,
            o: memory_state.o,
            d: w_loaded_data,
            insn: memory_state.insn,
            we: memory_state.we,
            div_res: w_divres,
            illegal_insn: memory_state.illegal_insn,
            cycle_status: memory_state.cycle_status,
            curr_cy: memory_state.curr_cy,
            insn_rd: memory_state.insn[11:7]
        };
      end
    end
  end

  wire [255:0] w_disasm;
  Disasm #(
      .PREFIX("W")
  ) disasm_1writeback (
      .insn  (writeback_state.insn),
      .disasm(w_disasm)
  );

  // writing it all out

  // for autograder
  always_comb begin
    if (writeback_state.illegal_insn) begin
      trace_writeback_pc   = 0;
      trace_writeback_insn = 0;
      // trace_writeback_pc   = writeback_state.pc;
      // trace_writeback_insn = writeback_state.insn;
    end else begin
      trace_writeback_pc   = writeback_state.pc;
      trace_writeback_insn = writeback_state.insn;
    end
    trace_writeback_cycle_status = writeback_state.cycle_status;
  end

  // send the outputs to the memory stage

  wire [6:0] w_insn_funct7;
  wire [4:0] w_insn_rs2;
  wire [4:0] w_insn_rs1;
  wire [2:0] w_insn_funct3;
  wire [4:0] w_insn_rd;
  wire [`OPCODE_SIZE] w_insn_opcode;

  assign {w_insn_funct7, w_insn_rs2, w_insn_rs1, w_insn_funct3, w_insn_rd, w_insn_opcode} = writeback_state.insn;

  logic [`REG_SIZE] w_mux_writeback;

  logic [3:0] taken;

  always_comb begin

    if (writeback_state.insn[6:0] == 7'b0_000_011) begin
      case (writeback_state.insn[14:12])
        3'b000: begin
          taken = 4'd1;
          // lb
          case (writeback_state.o[1:0])
            2'b00: w_mux_writeback = {{24{w_loaded_data[7]}}, w_loaded_data[7:0]};
            2'b01: w_mux_writeback = {{24{w_loaded_data[15]}}, w_loaded_data[15:8]};
            2'b10: w_mux_writeback = {{24{w_loaded_data[23]}}, w_loaded_data[23:16]};
            2'b11: w_mux_writeback = {{24{w_loaded_data[31]}}, w_loaded_data[31:24]};
          endcase
        end
        3'b001: begin
          taken = 4'd2;
          // lh
          case (writeback_state.o[1])
            1'b0: w_mux_writeback = {{16{w_loaded_data[15]}}, w_loaded_data[15:0]};
            1'b1: w_mux_writeback = {{16{w_loaded_data[31]}}, w_loaded_data[31:16]};
          endcase
        end
        3'b010: begin
          w_mux_writeback = w_loaded_data;
        end
        3'b100: begin
          taken = 4'd3;
          // lbu
          case (writeback_state.o[1:0])
            2'b00: w_mux_writeback = {24'b0, w_loaded_data[7:0]};
            2'b01: w_mux_writeback = {24'b0, w_loaded_data[15:8]};
            2'b10: w_mux_writeback = {24'b0, w_loaded_data[23:16]};
            2'b11: w_mux_writeback = {24'b0, w_loaded_data[31:24]};
          endcase
        end
        3'b101: begin
          taken = 4'd4;
          // lhu
          case (writeback_state.o[1])
            1'b0: w_mux_writeback = {16'b0, w_loaded_data[15:0]};
            1'b1: w_mux_writeback = {16'b0, w_loaded_data[31:16]};
          endcase
        end
        default: begin
          taken = 4'd5;
          w_mux_writeback = 32'b0;
        end
      endcase
    end else if (w_insn_opcode == OpcodeRegReg 
        && ((w_insn_funct3 == 3'b100
        || w_insn_funct3 == 3'b101
        || w_insn_funct3 == 3'b110
        || w_insn_funct3 == 3'b111
        ) && w_insn_funct7 == 7'h01)) begin
      taken = 4'd6;
      w_mux_writeback = writeback_state.div_res;
    end else begin
      taken = 4'd7;
      w_mux_writeback = writeback_state.o;
    end

    rf_rd = writeback_state.insn[11:7];
    rf_rd_data = w_mux_writeback;
    rf_we = writeback_state.we;
    // jmp opcode
  end

  always_comb begin
    if (writeback_state.insn[6:0] == 7'b1110011) begin
      halt = 1'b1;
    end else begin
      halt = 1'b0;
    end
  end


endmodule

module MemorySingleCycle #(
    parameter int NUM_WORDS = 512
) (
    // rst for both imem and dmem
    input wire rst,

    // clock for both imem and dmem. The memory reads/writes on @(negedge clk)
    input wire clk,

    // must always be aligned to a 4B boundary
    input wire [`REG_SIZE] pc_to_imem,

    // the value at memory location pc_to_imem
    output logic [`REG_SIZE] insn_from_imem,

    // must always be aligned to a 4B boundary
    input wire [`REG_SIZE] addr_to_dmem,

    // the value at memory location addr_to_dmem
    output logic [`REG_SIZE] load_data_from_dmem,

    // the value to be written to addr_to_dmem, controlled by store_we_to_dmem
    input wire [`REG_SIZE] store_data_to_dmem,

    // Each bit determines whether to write the corresponding byte of store_data_to_dmem to memory location addr_to_dmem.
    // E.g., 4'b1111 will write 4 bytes. 4'b0001 will write only the least-significant byte.
    input wire [3:0] store_we_to_dmem
);

  // memory is arranged as an array of 4B words
  logic [`REG_SIZE] mem[NUM_WORDS];

  initial begin
    $readmemh("mem_initial_contents.hex", mem, 0);
  end

  always_comb begin
    // memory addresses should always be 4B-aligned
    assert (pc_to_imem[1:0] == 2'b00);
    assert (addr_to_dmem[1:0] == 2'b00);
  end

  localparam int AddrMsb = $clog2(NUM_WORDS) + 1;
  localparam int AddrLsb = 2;

  always @(negedge clk) begin
    if (rst) begin
    end else begin
      insn_from_imem <= mem[{pc_to_imem[AddrMsb:AddrLsb]}];
    end
  end

  always @(negedge clk) begin
    if (rst) begin
    end else begin
      if (store_we_to_dmem[0]) begin
        mem[addr_to_dmem[AddrMsb:AddrLsb]][7:0] <= store_data_to_dmem[7:0];
      end
      if (store_we_to_dmem[1]) begin
        mem[addr_to_dmem[AddrMsb:AddrLsb]][15:8] <= store_data_to_dmem[15:8];
      end
      if (store_we_to_dmem[2]) begin
        mem[addr_to_dmem[AddrMsb:AddrLsb]][23:16] <= store_data_to_dmem[23:16];
      end
      if (store_we_to_dmem[3]) begin
        mem[addr_to_dmem[AddrMsb:AddrLsb]][31:24] <= store_data_to_dmem[31:24];
      end
      // dmem is "read-first": read returns value before the write
      load_data_from_dmem <= mem[{addr_to_dmem[AddrMsb:AddrLsb]}];
    end
  end
endmodule

/* This design has just one clock for both processor and memory. */
module RiscvProcessor (
    input wire clk,
    input wire rst,
    output logic halt,
    output wire [`REG_SIZE] trace_writeback_pc,
    output wire [`INSN_SIZE] trace_writeback_insn,
    output cycle_status_e trace_writeback_cycle_status
);

  // HW5 memory interface
  wire [`INSN_SIZE] insn_from_imem;
  wire [`REG_SIZE] pc_to_imem, mem_data_addr, mem_data_loaded_value, mem_data_to_write;
  wire [3:0] mem_data_we;
  MemorySingleCycle #(
      .NUM_WORDS(8192)
  ) the_mem (
      .rst                (rst),
      .clk                (clk),
      // imem is read-only
      .pc_to_imem         (pc_to_imem),
      .insn_from_imem     (insn_from_imem),
      // dmem is read-write
      .addr_to_dmem       (mem_data_addr),
      .load_data_from_dmem(mem_data_loaded_value),
      .store_data_to_dmem (mem_data_to_write),
      .store_we_to_dmem   (mem_data_we)
  );

  // HW6 memory interface
  axi_clkrst_if axi_cr (.ACLK(clk), .ARESETn(~rst));
  axi_if axi_data ();
  axi_if axi_insn ();
  MemoryAxiLite #(.NUM_WORDS(8192)) mem (
    .axi(axi_cr),
    .insn(axi_insn.subord),
    .data(axi_data.subord)
  );

  DatapathAxilMemory datapath (
      .clk(clk),
      .rst(rst),
      .imem(axi_insn.manager),
      .dmem(axi_data.manager),
      .halt(halt),
      .trace_writeback_pc(trace_writeback_pc),
      .trace_writeback_insn(trace_writeback_insn),
      .trace_writeback_cycle_status(trace_writeback_cycle_status)

  );

endmodule
