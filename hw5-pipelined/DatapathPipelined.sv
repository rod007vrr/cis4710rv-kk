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

  // TODO: your code here

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

  // the values below are only needed in HW5B

  /** a stall cycle that arose from a load-to-use stall */
  CYCLE_LOAD2USE = 8,
  /** a stall cycle that arose from a div/rem-to-use stall */
  CYCLE_DIV2USE = 16,
  /** a stall cycle that arose from a fence.i insn */
  CYCLE_FENCEI = 32
} cycle_status_e;

/** state at the start of Decode stage */
typedef struct packed {
  logic [`REG_SIZE] pc;
  logic [`INSN_SIZE] insn;
  cycle_status_e cycle_status;
} stage_decode_t;

typedef struct packed {
  logic [`REG_SIZE] pc;
  logic [`REG_SIZE] a;
  logic [`REG_SIZE] b;
  logic [`INSN_SIZE] insn;
  cycle_status_e cycle_status;
} stage_execute_t;

typedef struct packed {
  logic [`REG_SIZE] pc;
  logic [`REG_SIZE] o;
  logic [`REG_SIZE] b;
  logic [`INSN_SIZE] insn;
  cycle_status_e cycle_status;
} stage_memory_t;

typedef struct packed {
  logic [`REG_SIZE] pc;
  logic [`REG_SIZE] o;
  logic [`REG_SIZE] d;
  logic [`INSN_SIZE] insn;
  cycle_status_e cycle_status;
} stage_writeback_t;


module DatapathPipelined (
    input wire clk,
    input wire rst,
    output logic [`REG_SIZE] pc_to_imem,
    input wire [`INSN_SIZE] insn_from_imem,
    // dmem is read/write
    output logic [`REG_SIZE] addr_to_dmem,
    input wire [`REG_SIZE] load_data_from_dmem,
    output logic [`REG_SIZE] store_data_to_dmem,
    output logic [3:0] store_we_to_dmem,

    output logic halt,

    // The PC of the insn currently in Writeback. 0 if not a valid insn.
    output logic [`REG_SIZE] trace_writeback_pc,
    // The bits of the insn currently in Writeback. 0 if not a valid insn.
    output logic [`INSN_SIZE] trace_writeback_insn,
    // The status of the insn (or stall) currently in Writeback. See cycle_status_e enum for valid values.
    output cycle_status_e trace_writeback_cycle_status
);

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
  wire [`REG_SIZE] f_insn;
  cycle_status_e f_cycle_status;

  logic fd_clear_for_branch; // this is used when we clear the whole thing for branch
  logic [`REG_SIZE] fd_new_pc; //set when we branch

  // program counter
  always_ff @(posedge clk) begin
    if (rst) begin
      f_pc_current <= 32'd0;
      // NB: use CYCLE_NO_STALL since this is the value that will persist after the last reset cycle
      f_cycle_status <= CYCLE_NO_STALL;
    end else begin
      f_cycle_status <= CYCLE_NO_STALL;
      if (fd_clear_for_branch) begin
        f_pc_current <= fd_new_pc;
      end else begin
        f_pc_current <= f_pc_current + 4;
      end
    end
  end
  // send PC to imem
  assign pc_to_imem = f_pc_current;
  assign f_insn = insn_from_imem;

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
  stage_decode_t decode_state;
  always_ff @(posedge clk) begin
    if (rst) begin
      decode_state <= '{
        pc: 0,
        insn: 0,
        cycle_status: CYCLE_RESET
      };
    end else begin
      if (fd_clear_for_branch) begin
        decode_state <= '{
          pc: 0,
          insn: 0,
          cycle_status: CYCLE_TAKEN_BRANCH
        };
      end else begin
        decode_state <= '{
          pc: f_pc_current,
          insn: f_insn,
          cycle_status: f_cycle_status
        };
      end
    end
  end
  wire [255:0] d_disasm;
  Disasm #(
      .PREFIX("D")
  ) disasm_1decode (
      .insn  (decode_state.insn),
      .disasm(d_disasm)
  );

  // TODO: your code here, though you will also need to modify some of the code above
  // TODO: the testbench requires that your register file instance is named `rf`

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

  assign {x_insn_funct7, x_insn_rs2, x_insn_rs1, x_insn_funct3, x_insn_rd, x_insn_opcode} = decode_state.insn;

  // getting our outputs from memory
  logic [`REG_SIZE] x_rs1_data;
  logic [`REG_SIZE] x_rs2_data;

  always_comb begin
    rf_rs1 = x_insn_rs1;
    rf_rs2 = x_insn_rs2;
    
    //WD bypassing
    if (writeback_state.insn[11:7] == decode_state.insn[19:15] 
        && writeback_state.insn[11:7] != 5'b0) begin
      x_rs1_data = writeback_state.o;
    end else begin
      x_rs1_data = rf_rs1_data;
    end

    if (writeback_state.insn[11:7] == decode_state.insn[24:20] 
        && writeback_state.insn[11:7] != 5'b0) begin
      x_rs2_data = writeback_state.o;
    end else begin
      x_rs2_data = rf_rs2_data;
    end

  end

  stage_execute_t execute_state;
  always_ff @(posedge clk) begin
    if (rst) begin
      execute_state <= '{
        pc: 0,
        insn: 0,
        a: 0,
        b: 0,
        cycle_status: CYCLE_RESET
      };
    end else begin
      begin
        if (fd_clear_for_branch) begin 
          execute_state <= '{
            pc: fd_new_pc,
            a: 0,
            b: 0,
            insn: 0,
            cycle_status: CYCLE_TAKEN_BRANCH
          };
        end else begin 
          execute_state <= '{
            pc: decode_state.pc,
            a: x_rs1_data,
            b: x_rs2_data,
            insn: decode_state.insn,
            cycle_status: decode_state.cycle_status
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
  assign {imm_b[12], imm_b[10:5]} = m_insn_funct7, {imm_b[4:1], imm_b[11]} = m_insn_rd, imm_b[0] = 1'b0;
  wire [`REG_SIZE] imm_b_sext = {{19{imm_b[12]}}, imm_b[12:0]};

  wire [20:0] imm_j;
  assign {imm_j[20], imm_j[10:1], imm_j[11], imm_j[19:12], imm_j[0]} = {execute_state.insn[31:12], 1'b0};
  wire [`REG_SIZE] imm_j_sext = {{11{imm_j[20]}}, imm_j[20:0]};


  logic [`REG_SIZE] m_bypass_a;
  logic [`REG_SIZE] m_bypass_b;

  logic [63:0] mul_h, mul_hsu, mul_hu;


  always_comb begin
    // the problem is here because its 0 initialized 

    // WX/MX BYPASSING

    if (writeback_state.insn[11:7] == execute_state.insn[19:15] 
        && writeback_state.insn[11:7] != 5'b0) begin
      m_bypass_a = writeback_state.o;
    end else if (memory_state.insn[11:7] == execute_state.insn[19:15] 
        && memory_state.insn[11:7] != 5'b0) begin
      m_bypass_a = memory_state.o;
    end else begin
      m_bypass_a = execute_state.a;
    end

    if (writeback_state.insn[11:7] == execute_state.insn[24:20] 
        && writeback_state.insn[11:7] != 5'b0) begin
      m_bypass_b = writeback_state.o;
    end else if (memory_state.insn[11:7] == execute_state.insn[24:20] 
        && memory_state.insn[11:7] != 5'b0) begin
      m_bypass_b = memory_state.o;
    end else begin
      m_bypass_b = execute_state.b;
    end


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

    case (m_insn_opcode)
      OpcodeLui: begin
        m_output = {execute_state.insn[31:12], 12'd0};
      end
      OpcodeRegImm: begin
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
          illegal_insn = 1'b1;
        end
      end
      OpcodeRegReg: begin
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
          mul_hsu = {{32{m_bypass_a[31]}}, m_bypass_a} * {32'b0, m_bypass_b};
          m_output = mul_hsu[63:32];
        end else if (insn_mulhu) begin
          mul_hu = m_bypass_a * m_bypass_b;
          m_output = mul_hu[63:32];
        end 
      end
      OpcodeJal: begin
        if (insn_jal) begin
          fd_new_pc = execute_state.pc + imm_j_sext;
          fd_clear_for_branch = 1'b1;
          m_output = execute_state.pc + 4;
        end else begin
          illegal_insn = 1'b1;
        end
      end
      OpcodeJalr: begin
        if (insn_jalr) begin
          fd_new_pc = (m_bypass_a + imm_i_sext) & ~(32'h1);
          fd_clear_for_branch = 1'b1;
          m_output = execute_state.pc + 4;
        end else begin
          illegal_insn = 1'b1;
        end
      end
      OpcodeBranch: begin
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
      default: begin
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
        cycle_status: CYCLE_RESET
      };
    end else begin
      begin
        memory_state <= '{
          pc: execute_state.pc,
          insn: execute_state.insn,
          o: m_output,
          b: execute_state.b,
          cycle_status: execute_state.cycle_status
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

  always_comb begin
    w_loaded_data = 0;
  end

  stage_writeback_t writeback_state;
  always_ff @(posedge clk) begin
    if (rst) begin
      writeback_state <= '{
        pc: 0,
        insn: 0,
        o: 0,
        d: 0,
        cycle_status: CYCLE_RESET
      };
    end else begin
      begin
        writeback_state <= '{
          pc: memory_state.pc,
          o: memory_state.o,
          d: w_loaded_data,
          insn: memory_state.insn,
          cycle_status: memory_state.cycle_status
        };
      end
    end
  end

  // for autograder
  assign trace_writeback_pc = writeback_state.pc;
  assign trace_writeback_insn = writeback_state.insn;
  assign trace_writeback_cycle_status = writeback_state.cycle_status;

  // send the outputs to the memory stage

  wire [6:0] w_insn_funct7;
  wire [4:0] w_insn_rs2;
  wire [4:0] w_insn_rs1;
  wire [2:0] w_insn_funct3;
  wire [4:0] w_insn_rd;
  wire [`OPCODE_SIZE] w_insn_opcode;

  assign {w_insn_funct7, w_insn_rs2, w_insn_rs1, w_insn_funct3, w_insn_rd, w_insn_opcode} = writeback_state.insn;

  logic [`REG_SIZE] w_mux_writeback;

  assign w_mux_writeback = writeback_state.o;

  always_comb begin
    rf_rd = writeback_state.insn[11:7];
    rf_rd_data = w_mux_writeback;
    // jmp opcode
    if (writeback_state.insn[6:0] == 7'b1100011) begin
      rf_we = 1'b0;
    end else begin
      rf_we = 1'b1;
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
    input  wire  clk,
    input  wire  rst,
    output logic halt,
    output wire [`REG_SIZE] trace_writeback_pc,
    output wire [`INSN_SIZE] trace_writeback_insn,
    output cycle_status_e trace_writeback_cycle_status
);

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

  DatapathPipelined datapath (
      .clk(clk),
      .rst(rst),
      .pc_to_imem(pc_to_imem),
      .insn_from_imem(insn_from_imem),
      .addr_to_dmem(mem_data_addr),
      .store_data_to_dmem(mem_data_to_write),
      .store_we_to_dmem(mem_data_we),
      .load_data_from_dmem(mem_data_loaded_value),
      .halt(halt),
      .trace_writeback_pc(trace_writeback_pc),
      .trace_writeback_insn(trace_writeback_insn),
      .trace_writeback_cycle_status(trace_writeback_cycle_status)
  );

endmodule
