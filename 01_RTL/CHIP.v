//----------------------------- DO NOT MODIFY THE I/O INTERFACE!! ------------------------------//
module CHIP #(                                                                                  //
    parameter BIT_W = 32                                                                        //
)(                                                                                              //
    // clock                                                                                    //
        input               i_clk,                                                              //
        input               i_rst_n,                                                            //
    // instruction memory                                                                       //
        input  [BIT_W-1:0]  i_IMEM_data,                                                        //
        output [BIT_W-1:0]  o_IMEM_addr,                                                        //
        output              o_IMEM_cen,                                                         //
    // data memory                                                                              //
        input               i_DMEM_stall,                                                       //
        input  [BIT_W-1:0]  i_DMEM_rdata,                                                       //
        output              o_DMEM_cen,                                                         //
        output              o_DMEM_wen,                                                         //
        output [BIT_W-1:0]  o_DMEM_addr,                                                        //
        output [BIT_W-1:0]  o_DMEM_wdata,                                                       //
    // finnish procedure                                                                        //
        output              o_finish,                                                           //
    // cache                                                                                    //
        input               i_cache_finish,                                                     //
        output              o_proc_finish                                                       //
);                                                                                              //
//----------------------------- DO NOT MODIFY THE I/O INTERFACE!! ------------------------------//

// ------------------------------------------------------------------------------------------------------------------------------------------------------
// Parameters
// ------------------------------------------------------------------------------------------------------------------------------------------------------

    // TODO: any declaration
        // auipc
        parameter auipc_opcode = 7'b0010111
        // jal
        parameter jal_opcode   = 7'b1101111
        // jalr
        parameter jalr_opcode  = 7'b1100111
        // add
        parameter add_funct7   = 7'b0000000
        parameter add_funct3   = 3'b000
        parameter add_opcode   = 7'b0110011
        // sub
        parameter sub_funct7   = 7'b0100000
        parameter sub_funct3   = 3'b000
        parameter sub_opcode   = 7'b0110011
        // and
        parameter and_funct7   = 7'b0000000
        parameter and_funct3   = 3'b111
        parameter and_opcode   = 7'b0110011
        // xor
        parameter xor_funct7   = 7'b0000000
        parameter xor_funct3   = 3'b100
        parameter xor_opcode   = 7'b0110011
        // addi
        parameter addi_funct3  = 3'b000
        parameter addi_opcode  = 7'b0010011
        // slli
        parameter slli_funct3  = 3'b001
        parameter slli_opcode  = 7'b0010011
        // slti
        parameter slti_funct3  = 3'b010
        parameter slti_opcode  = 7'b0010011
        // srai
        parameter srai_funct7  = 7'b0100000
        parameter srai_funct3  = 3'b101
        parameter srai_opcode  = 7'b0010011
        // lw
        parameter lw_funct3    = 3'b010
        parameter lw_opcode    = 7'b0000011
        // sw
        parameter sw_funct3    = 3'b010
        parameter sw_opcode    = 7'b0100011
        // mul
        parameter mul_funct3   = 3'b000
        parameter mul_opcode   = 7'b0110011
        // beq
        parameter beq_funct3   = 3'b000
        parameter beq_opcode   = 7'b1100011
        // bge
        parameter bge_funct3   = 3'b101
        parameter bge_opcode   = 7'b1100011
        // blt
        parameter blt_funct3   = 3'b100
        parameter blt_opcode   = 7'b1100011
        // bne
        parameter bne_funct3   = 3'b001
        parameter bne_opcode   = 7'b1100011
        // ecall
        parameter ecall        = 32'b0000_0000_0001_0000_0000_0000_0111_0011

// ------------------------------------------------------------------------------------------------------------------------------------------------------
// Wires and Registers
// ------------------------------------------------------------------------------------------------------------------------------------------------------
    
    // TODO: any declaration
        reg [BIT_W-1:0] PC, next_PC;
        wire mem_cen, mem_wen;
        wire [BIT_W-1:0] mem_addr, mem_wdata, mem_rdata;
        wire mem_stall;

        reg [BIT_W-1:0] rdata1, rdata2;

        wire ALUSrc;
        wire MemtoReg;
        wire RegWrite;
        wire MemRead;
        wire MemWrite;
        wire Branch;
        wire [1:0] ALUOp;
        wire [3:0] ALU_control_input;

// ------------------------------------------------------------------------------------------------------------------------------------------------------
// Continuous Assignment
// ------------------------------------------------------------------------------------------------------------------------------------------------------

    // TODO: any wire assignment
        assign ALUSrc = (i_IMEM_data[6:0]==7'b0000011) || (i_IMEM_data[6:0]==7'b0100011);
        assign MemtoReg = (i_IMEM_data[6:0]==7'b0000011);
        assign RegWrite = (i_IMEM_data[6:0]==7'b0110011) || (i_IMEM_data[6:0]==7'b0000011);
        assign MemRead = (i_IMEM_data[6:0]==7'b0000011);
        assign MemWrite = (i_IMEM_data[6:0]==7'b0100011);
        assign Branch = (i_IMEM_data[6:0]==7'b1100011);
        assign ALUOp[1] = (i_IMEM_data[6:0]==7'b0110011);
        assign ALUOp[0] = (i_IMEM_data[6:0]==7'b1100011);
        
        assign ALU_control_input = (ALUOp==2'b00 ? 4'b0010 : (ALUOp[0]==1'b1 ? 4'b0110 : (i_IMEM_data[14:12]==3'b000 ? 4'b0010 : \
            (i_IMEM_data[30]==1'b1 ? 4'b0110 : (i_IMEM_data[[14:12]==3'b111 ? 4'b0000 : 4'b0001])))));

// ------------------------------------------------------------------------------------------------------------------------------------------------------
// Submoddules
// ------------------------------------------------------------------------------------------------------------------------------------------------------

    // TODO: Reg_file wire connection
    Reg_file reg0(               
        .i_clk  (i_clk),             
        .i_rst_n(i_rst_n),         
        .wen    (RegWrite),          
        .rs1    (i_IMEM_data[19:15]),                
        .rs2    (i_IMEM_data[24:20]),                
        .rd     (i_IMEM_data[11:7]),                 
        .wdata  (mem_wdata),             
        .rdata1 (rdata1),           
        .rdata2 (rdata2)
    );

// ------------------------------------------------------------------------------------------------------------------------------------------------------
// Always Blocks
// ------------------------------------------------------------------------------------------------------------------------------------------------------
    
    // Todo: any combinational/sequential circuit
    always@(*)begin
    end

    always @(posedge i_clk or negedge i_rst_n) begin
        if (!i_rst_n) begin
            PC <= 32'h00010000; // Do not modify this value!!!
        end
        else begin
            PC <= next_PC;
        end
    end
endmodule

module Reg_file(i_clk, i_rst_n, wen, rs1, rs2, rd, wdata, rdata1, rdata2);
   
    parameter BITS = 32;
    parameter word_depth = 32;
    parameter addr_width = 5; // 2^addr_width >= word_depth
    
    input i_clk, i_rst_n, wen; // wen: 0:read | 1:write
    input [BITS-1:0] wdata;
    input [addr_width-1:0] rs1, rs2, rd;

    output [BITS-1:0] rdata1, rdata2;

    reg [BITS-1:0] mem [0:word_depth-1];
    reg [BITS-1:0] mem_nxt [0:word_depth-1];

    integer i;

    assign rdata1 = mem[rs1];
    assign rdata2 = mem[rs2];

    always @(*) begin
        for (i=0; i<word_depth; i=i+1)
            mem_nxt[i] = (wen && (rd == i)) ? wdata : mem[i];
    end

    always @(posedge i_clk or negedge i_rst_n) begin
        if (!i_rst_n) begin
            mem[0] <= 0;
            for (i=1; i<word_depth; i=i+1) begin
                case(i)
                    32'd2: mem[i] <= 32'hbffffff0;
                    32'd3: mem[i] <= 32'h10008000;
                    default: mem[i] <= 32'h0;
                endcase
            end
        end
        else begin
            mem[0] <= 0;
            for (i=1; i<word_depth; i=i+1)
                mem[i] <= mem_nxt[i];
        end       
    end
endmodule

module MULDIV_unit(
    // TODO: port declaration
        input                       i_clk,   // clock
        input                       i_rst_n, // reset

        input                       i_valid, // input valid signal
        input [DATA_W - 1 : 0]      i_A,     // input operand A
        input [DATA_W - 1 : 0]      i_B,     // input operand B
        input [         2 : 0]      i_inst,  // instruction

        output [2*DATA_W - 1 : 0]   o_data,  // output value
        output                      o_done   // output valid signal
    );
    // Todo: HW2
endmodule

module Cache#(
        parameter BIT_W = 32,
        parameter ADDR_W = 32
    )(
        input i_clk,
        input i_rst_n,
        // processor interface
            input i_proc_cen,
            input i_proc_wen,
            input [ADDR_W-1:0] i_proc_addr,
            input [BIT_W-1:0]  i_proc_wdata,
            output [BIT_W-1:0] o_proc_rdata,
            output o_proc_stall,
            input i_proc_finish,
            output o_cache_finish,
        // memory interface
            output o_mem_cen,
            output o_mem_wen,
            output [ADDR_W-1:0] o_mem_addr,
            output [BIT_W*4-1:0]  o_mem_wdata,
            input [BIT_W*4-1:0] i_mem_rdata,
            input i_mem_stall,
            output o_cache_available
    );

    assign o_cache_available = 0; // change this value to 1 if the cache is implemented

    //------------------------------------------//
    //          default connection              //
    assign o_mem_cen = i_proc_cen;              //
    assign o_mem_wen = i_proc_wen;              //
    assign o_mem_addr = i_proc_addr;            //
    assign o_mem_wdata = i_proc_wdata;          //
    assign o_proc_rdata = i_mem_rdata[0+:BIT_W];//
    assign o_proc_stall = i_mem_stall;          //
    //------------------------------------------//

    // Todo: BONUS

endmodule