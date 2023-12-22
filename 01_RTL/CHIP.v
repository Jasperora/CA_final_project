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
        output              o_proc_finish                                                       // TODO: call cache to clean all dirty blocks
);                                                                                              //
//----------------------------- DO NOT MODIFY THE I/O INTERFACE!! ------------------------------//

// ------------------------------------------------------------------------------------------------------------------------------------------------------
// Parameters
// ------------------------------------------------------------------------------------------------------------------------------------------------------
    // auipc
    parameter auipc_opcode = 7'b0010111;
    // jal
    parameter jal_opcode   = 7'b1101111;
    // jalr
    parameter jalr_opcode  = 7'b1100111;
    // add
    parameter add_funct7   = 7'b0000000;
    parameter add_funct3   = 3'b000;
    parameter add_opcode   = 7'b0110011;
    // sub
    parameter sub_funct7   = 7'b0100000;
    parameter sub_funct3   = 3'b000;
    parameter sub_opcode   = 7'b0110011;
    // and
    parameter and_funct7   = 7'b0000000;
    parameter and_funct3   = 3'b111;
    parameter and_opcode   = 7'b0110011;
    // xor
    parameter xor_funct7   = 7'b0000000;
    parameter xor_funct3   = 3'b100;
    parameter xor_opcode   = 7'b0110011;
    // addi
    parameter addi_funct3  = 3'b000;
    parameter addi_opcode  = 7'b0010011;
    // slli
    parameter slli_funct3  = 3'b001;
    parameter slli_opcode  = 7'b0010011;
    // slti
    parameter slti_funct3  = 3'b010;
    parameter slti_opcode  = 7'b0010011;
    // srai
    parameter srai_funct7  = 7'b0100000;
    parameter srai_funct3  = 3'b101;
    parameter srai_opcode  = 7'b0010011;
    // lw
    parameter lw_funct3    = 3'b010;
    parameter lw_opcode    = 7'b0000011;
    // sw
    parameter sw_funct3    = 3'b010;
    parameter sw_opcode    = 7'b0100011;
    // mul
    parameter mul_funct7   = 7'b0000001;
    parameter mul_funct3   = 3'b000;
    parameter mul_opcode   = 7'b0110011;
    // beq
    parameter beq_funct3   = 3'b000;
    parameter beq_opcode   = 7'b1100011;
    // bge
    parameter bge_funct3   = 3'b101;
    parameter bge_opcode   = 7'b1100011;
    // blt
    parameter blt_funct3   = 3'b100;
    parameter blt_opcode   = 7'b1100011;
    // bne
    parameter bne_funct3   = 3'b001;
    parameter bne_opcode   = 7'b1100011;
    // ecall
    parameter ecall_opcode = 7'b1110011;
    parameter ecall        = 32'b0000_0000_0001_0000_0000_0000_0111_0011;

// ------------------------------------------------------------------------------------------------------------------------------------------------------
// Wires and Registers
// ------------------------------------------------------------------------------------------------------------------------------------------------------
    // instruction memory
    reg [BIT_W-1:0] PC, PC_nxt;
    wire mem_cen, mem_wen;
    wire [BIT_W-1:0] mem_addr, mem_wdata, mem_rdata;
    wire mem_stall;

    // register
    reg [BIT_W-1:0] imm;
    wire [BIT_W-1:0] rdata1, rdata2;
    reg [BIT_W-1:0] rdatad, rdatad_nxt;

    // data memory
    reg [BIT_W-1:0] DMEM_addr, DMEM_addr_nxt;
    reg [BIT_W-1:0] DMEM_wdata, DMEM_wdata_nxt;
    reg [BIT_W-1:0] DMEM_rdata, DMEM_rdata_nxt;

    // instruction
    wire ALUSrc;
    wire MemtoReg;
    wire RegWrite;
    wire MemRead;
    wire MemWrite;
    wire Branch;
    wire [1:0] ALUOp;
    wire [3:0] ALU_control_input;

    // operation
    wire muldiv_done;
    wire [BIT_W-1:0] muldiv_result;
    reg muldiv_valid, muldiv_valid_nxt;

    // finish procedure
    reg finish, finish_nxt;

// ------------------------------------------------------------------------------------------------------------------------------------------------------
// Continuous Assignment
// ------------------------------------------------------------------------------------------------------------------------------------------------------
    // instruction memory
    assign o_IMEM_addr = PC;
    assign o_IMEM_cen = 1'b1; // load instruction

    // control signal
    assign ALUSrc = (i_IMEM_data[6:0]==lw_opcode) || (i_IMEM_data[6:0]==sw_opcode);
    assign MemtoReg = (i_IMEM_data[6:0]==lw_opcode);
    assign RegWrite = (i_IMEM_data[6:0]==add_opcode) || (i_IMEM_data[6:0]==addi_opcode) || (i_IMEM_data[6:0]==lw_opcode) || (i_IMEM_data[6:0]==auipc_opcode) || (i_IMEM_data[6:0]==jal_opcode) || (i_IMEM_data[6:0]==jalr_opcode);
    assign MemRead = (i_IMEM_data[6:0]==lw_opcode);
    assign MemWrite = (i_IMEM_data[6:0]==sw_opcode);
    assign Branch = (i_IMEM_data[6:0]==beq_opcode);
    assign ALUOp[1] = (i_IMEM_data[6:0]==add_opcode);
    assign ALUOp[0] = (i_IMEM_data[6:0]==beq_opcode);   
    assign ALU_control_input = (ALUOp==2'b00 ? 4'b0010 : (ALUOp[0]==1'b1 ? 4'b0110 : (i_IMEM_data[14:12]==3'b000 ? 4'b0010 : (i_IMEM_data[30]==1'b1 ? 4'b0110 : (i_IMEM_data[14:12]==3'b111 ? 4'b0000 : 4'b0001)))));

    // data memory
    assign o_DMEM_cen = MemtoReg || MemRead || MemWrite; // TODO: o_DMEM_cen
    assign o_DMEM_wen = MemWrite ? 1 : 0;   // TODO: o_DMEM_wen
    assign o_DMEM_addr = DMEM_addr; // TODO: o_DMEM_addr
    assign o_DMEM_wdata = DMEM_wdata;   // TODO: o_DMEM_wdata

    // finish
    // assign o_finish = i_cache_finish;
    // assign o_proc_finish = finish;
    assign o_finish = finish;

// ------------------------------------------------------------------------------------------------------------------------------------------------------
// Submoddules
// ------------------------------------ ------------------------------------------------------------------------------------------------------------------
    Reg_file reg0(               
        .i_clk  (i_clk),             
        .i_rst_n(i_rst_n),         
        .wen    (RegWrite),          
        .rs1    (i_IMEM_data[19:15]),                
        .rs2    (i_IMEM_data[24:20]),                
        .rd     (i_IMEM_data[11:7]),                 
        .wdata  (rdatad_nxt),             
        .rdata1 (rdata1),           
        .rdata2 (rdata2)
    );

    MULDIV_unit muldiv0(
        .i_clk(i_clk),
        .i_rst_n(i_rst_n),
        .i_valid(muldiv_valid),
        .i_A(rdata1),
        .i_B(rdata2),
        .o_data(muldiv_result),
        .o_done(muldiv_done)
    );

// ------------------------------------------------------------------------------------------------------------------------------------------------------
// Always Blocks
// ------------------------------------------------------------------------------------------------------------------------------------------------------
    always @(*) begin
        muldiv_valid_nxt = muldiv_valid;
        DMEM_wdata_nxt = DMEM_wdata;
        DMEM_addr_nxt = DMEM_addr;
        PC_nxt = PC;
        rdatad_nxt = rdatad;
        finish_nxt = finish;

        case (i_IMEM_data[6:0])
            auipc_opcode: begin
                // $display("auipc");
                // auipc
                imm = {i_IMEM_data[31:12], 12'b0};
                rdatad_nxt = $signed(PC) + $signed(imm);
                PC_nxt = $signed(PC) + $signed(4);
            end
            jal_opcode: begin
                // jal
                imm = {{11{i_IMEM_data[31]}}, i_IMEM_data[31], i_IMEM_data[19:12], i_IMEM_data[20], i_IMEM_data[30:21], 1'b0};
                rdatad_nxt = $signed(PC) + $signed(4);
                PC_nxt = $signed(PC) + $signed(imm);
            end
            jalr_opcode: begin
                // jalr
                imm = {20'b0, i_IMEM_data[31:20]};
                rdatad_nxt = $signed(PC) + $signed(4);
                PC_nxt = $signed(rdata1) + $signed(imm);
            end
            add_opcode: begin
                case({i_IMEM_data[31:25], i_IMEM_data[14:12]})
                    {add_funct7, add_funct3}: begin
                        // add
                        rdatad_nxt = $signed(rdata1) + $signed(rdata2);
                        PC_nxt = $signed(PC) + $signed(4);
                    end
                    {sub_funct7, sub_funct3}: begin
                        // sub
                        rdatad_nxt = $signed(rdata1) - $signed(rdata2);
                        PC_nxt = $signed(PC) + $signed(4);
                    end
                    {and_funct7, and_funct3}: begin
                        // and
                        rdatad_nxt = rdata1 & rdata2;
                        PC_nxt = $signed(PC) + $signed(4);
                    end
                    {xor_funct7, xor_funct3}: begin
                        // xor
                        rdatad_nxt = rdata1 ^ rdata2;
                        PC_nxt = $signed(PC) + $signed(4);
                    end
                    {mul_funct7, mul_funct3}: begin
                        // mul
                        rdatad_nxt = muldiv_done ? muldiv_result : rdatad;
                        PC_nxt = muldiv_done ? ($signed(PC) + $signed(4)) : PC;
                        muldiv_valid_nxt = 1;
                    end
                    default: begin
                        rdatad_nxt = rdatad;
                        PC_nxt = $signed(PC) + $signed(4);
                    end
                endcase
            end
            addi_opcode: begin
                case(i_IMEM_data[14:12])
                    addi_funct3: begin
                        // addi
                        imm = {20'b0, i_IMEM_data[31:20]};
                        rdatad_nxt = $signed(rdata1) + $signed(imm);
                        PC_nxt = $signed(PC) + $signed(4);
                    end
                    slli_funct3: begin
                        // slli
                        imm = i_IMEM_data[25:20];
                        rdatad_nxt = rdata1 << imm;
                        PC_nxt = $signed(PC) + $signed(4);
                    end
                    slti_funct3: begin
                        // slti
                        imm = {20'b0, i_IMEM_data[31:20]};
                        rdatad_nxt = (rdata1 < imm) ? 1 : 0;
                        PC_nxt = $signed(PC) + $signed(4);
                    end
                    srai_funct3: begin
                        // srai
                        imm = i_IMEM_data[24:20];
                        rdatad_nxt = rdata1 >>> imm;
                        PC_nxt = $signed(PC) + $signed(4);
                    end
                    default: begin
                        rdatad_nxt = rdatad;
                        PC_nxt = $signed(PC) + $signed(4);
                    end
                endcase
            end
            lw_opcode: begin
                // lw
                if (i_DMEM_stall) begin // TODO: i_DMEM_stall
                    imm = {{20{i_IMEM_data[31]}}, i_IMEM_data[31:20]};
                    DMEM_addr_nxt = $signed(rdata1) + $signed(imm);
                    rdatad_nxt = rdatad;
                    PC_nxt = PC;
                end
                else begin
                    imm = {{20{i_IMEM_data[31]}}, i_IMEM_data[31:20]};
                    DMEM_addr_nxt = $signed(rdata1) + $signed(imm);
                    rdatad_nxt = i_DMEM_rdata; // TODO: i_DMEM_rdata
                    PC_nxt = $signed(PC) + $signed(4);
                end
            end
            sw_opcode: begin
                if (i_DMEM_stall) begin // TODO: i_DMEM_stall
                    imm = {{20'b0}, i_IMEM_data[31:25], i_IMEM_data[11:7]};
                    DMEM_addr_nxt = rdata1 + imm;
                    DMEM_wdata_nxt = rdata2;
                    PC_nxt = PC;
                end
                else begin
                    DMEM_addr_nxt = DMEM_addr;
                    DMEM_wdata_nxt = DMEM_wdata;
                    PC_nxt = $signed(PC) + $signed(4);
                end
            end
            bge_opcode: begin
                case(i_IMEM_data[6:0])
                    bge_funct3: begin
                        // bge
                        imm = {20'b0, i_IMEM_data[31], i_IMEM_data[8], i_IMEM_data[30:25], i_IMEM_data[12:9]};
                        PC_nxt = ($signed(rdata1) >= $signed(rdata2)) ? ($signed(PC) + $signed({imm, 1'b0})) : $signed(PC) + $signed(4);
                    end
                    beq_funct3: begin
                        // beq
                        imm = {20'b0, i_IMEM_data[31], i_IMEM_data[8], i_IMEM_data[30:25], i_IMEM_data[12:9]};
                        PC_nxt = ($signed(rdata1) == $signed(rdata2)) ? ($signed(PC) + $signed({imm, 1'b0})) : $signed(PC) + $signed(4);
                    end
                    blt_funct3: begin
                        // blt
                        imm = {20'b0, i_IMEM_data[31], i_IMEM_data[8], i_IMEM_data[30:25], i_IMEM_data[12:9]};
                        PC_nxt = ($signed(rdata1) < $signed(rdata2)) ? ($signed(PC) + $signed({imm, 1'b0})) : $signed(PC) + $signed(4);
                    end
                    bne_funct3: begin
                        // bne
                        imm = {20'b0, i_IMEM_data[31], i_IMEM_data[8], i_IMEM_data[30:25], i_IMEM_data[12:9]};
                        PC_nxt = ($signed(rdata1) != $signed(rdata2)) ? ($signed(PC) + $signed({imm, 1'b0})) : $signed(PC) + $signed(4);
                    end
                    default: begin
                        PC_nxt = $signed(PC) + $signed(4);
                    end
                endcase
            end
            ecall_opcode: begin
                finish_nxt = 1;
            end
            default: begin
                PC_nxt = $signed(PC) + $signed(4);
            end
        endcase
    end
    

    always @(posedge i_clk or negedge i_rst_n) begin
        // $display("hello");
        if (!i_rst_n) begin

            PC <= 32'h00010000; // Do not modify this value!!!
            
            rdatad <= 32'b0;
            DMEM_addr <= 0;
            DMEM_wdata <= 0;
            DMEM_rdata <= 0;

            finish <= 0;
            muldiv_valid <= 0;
        end
        else begin

            PC <= PC_nxt;

            rdatad <= rdatad_nxt;
            DMEM_addr <= DMEM_addr_nxt;
            DMEM_wdata <= DMEM_wdata_nxt;
            DMEM_rdata <= DMEM_rdata_nxt;

            finish <= finish_nxt;
            muldiv_valid <= muldiv_valid_nxt;
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

module MULDIV_unit#(
    parameter BIT_W = 32    
)(
    // REVIEW: port declaration
        input                       i_clk,   // clock
        input                       i_rst_n, // reset

        input                       i_valid, // input valid signal
        input [BIT_W - 1 : 0]       i_A,     // input operand A
        input [BIT_W - 1 : 0]       i_B,     // input operand B

        output [BIT_W - 1 : 0]      o_data,  // output value
        output                      o_done   // output valid signal
);
    // Do not Modify the above part !!!
    // Parameters
    parameter S_IDLE           = 2'd0;
    parameter S_MULTI_CYCLE_OP = 2'd2;

    // Wires & Regs
    // state
    reg  [           1: 0] state, state_nxt; // remember to expand the bit width if you want to add more states!
    // load input
    reg  [     BIT_W-1: 0] operand_a, operand_a_nxt;
    reg  [     BIT_W-1: 0] operand_b, operand_b_nxt;
    reg  [           2: 0] inst, inst_nxt;

    // Wire Assignments
    // Counter
    reg  [4:0] cnt, cnt_nxt;
    // Output
    reg  [2*BIT_W - 1 : 0] o_data_cur, o_data_nxt;
    reg                     o_done_cur, o_done_nxt;
    
    // Always Combination
    // load input
    always @(*) begin
        if (i_valid) begin
            operand_a_nxt = i_A;
            operand_b_nxt = i_B;
        end
        else begin
            operand_a_nxt = operand_a;
            operand_b_nxt = operand_b;
        end
    end
    // FSM
    always @(*) begin
        case(state)
            S_IDLE           : begin
                if (i_valid) begin
                    state_nxt = S_MULTI_CYCLE_OP;
                end
                else begin // stay in S_IDLE
                    state_nxt = state;
                end
            end
            S_MULTI_CYCLE_OP : begin
                if (cnt==5'd31) begin
                    state_nxt = S_IDLE;
                end
                else begin
                    state_nxt = S_MULTI_CYCLE_OP;
                end
            end
            default : state_nxt = state;
        endcase
    end
    // Counter
    always @(negedge i_clk) begin
        if (state==S_MULTI_CYCLE_OP) begin
            cnt_nxt = cnt + 1;
        end
        else begin
            cnt_nxt = cnt;
        end
    end
    // ALU output
    always @(*) begin
        if (state==S_MULTI_CYCLE_OP) begin // MUL A: multiplicand, B: multiplier
            if (cnt==0) begin
                if (operand_b[0]==1)begin
                    o_data_nxt = {operand_a, operand_b} >> 1;
                end
                else begin
                    o_data_nxt = {{BIT_W{1'b0}}, operand_b} >> 1;
                end
                o_done_nxt = 0;
            end
            else if (cnt<31) begin
                if (o_data_cur[0]==1) begin
                    o_data_nxt = {{1'b0, o_data_cur[2*BIT_W-1:BIT_W]} + {1'b0, operand_a}, o_data_cur[BIT_W-1:1]};
                end
                else begin
                    o_data_nxt = o_data_cur >> 1;
                end
                o_done_nxt = 0;
            end
            else begin
                if (o_data_cur[0]==1) begin
                    o_data_nxt = {{1'b0, o_data_cur[2*BIT_W-1:BIT_W]} + {1'b0, operand_a}, o_data_cur[BIT_W-1:1]};
                end
                else begin
                    o_data_nxt = o_data_cur >> 1;
                end
                o_done_nxt = 1;
            end
        end
        else begin
            o_data_nxt = 0;
            o_done_nxt = 0;
        end
    end
    
    // output valid signal
    assign o_data = o_data_cur[31:0];
    assign o_done = o_done_cur;

    // Sequential always block
    always @(posedge i_clk or negedge i_rst_n) begin
        if (!i_rst_n) begin
            state       <= S_IDLE;
            operand_a   <= 0;
            operand_b   <= 0;
            cnt         <= 0;
            o_data_cur  <= 0;
            o_done_cur  <= 0;
        end
        else begin
            state       <= state_nxt;
            operand_a   <= operand_a_nxt;
            operand_b   <= operand_b_nxt;
            cnt         <= cnt_nxt;
            o_data_cur  <= o_data_nxt;
            o_done_cur  <= o_done_nxt;
        end
    end
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
        output o_cache_available,
        // others
        input  [ADDR_W-1: 0] i_offset
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

    // // registers
    // reg [2:0] state, state_nxt;
    // reg [1:0] mode, mode_nxt;
    
    // // data/address
    // reg [ADDR_W-1:0] addr, addr_nxt;
    // reg [BIT_W-1:0] rdata, rdata_nxt;
    // reg [BIT_W-1:0]  wdata, wdata_nxt;
    // reg [ADDR_W-1:0] mem_addr, mem_addr_nxt;
    // reg [BIT_W*4-1:0] mem_rdata, mem_rdata_nxt;
    // reg [BIT_W*4-1:0]  mem_wdata, mem_wdata_nxt;
    // // control signals
    // reg stall, stall_nxt;
    // reg finish, finish_nxt;
    // reg cen, cen_nxt;
    // reg wen, wen_nxt;

    // // processor
    // assign o_proc_rdata = rdata;
    // assign o_proc_stall = stall;
    // assign o_cache_finish = finish;
    // // memory
    // assign o_mem_cen = cen;
    // assign o_mem_wen = wen;
    // assign o_mem_addr = mem_addr;
    // assign o_mem_wdata = mem_wdata;

    // // parameters
    // // state
    // parameter S_IDLE    = 3'd0;
    // parameter S_WRITE   = 3'd1;
    // parameter S_WB      = 3'd2;
    // parameter S_ALLO    = 3'd3;
    // parameter S_READ    = 3'd4;
    // parameter S_CLEAN   = 3'd5; // write baack all dirty blocks when i_proc_finish=1
    // // mode
    // parameter M_READ    = 2'd0;
    // parameter M_WRITE   = 2'd1;
    // parameter M_CLEAN   = 2'd2;

    // // entries
    // reg [0:15] v, v_nxt; // valid bit
    // reg [0:15] dirty, dirty_nxt;  // dirty bit
    // reg [31:8] tag [0:15], tag_nxt [0:15];
    // reg [BIT_W*4-1:0] entry [0:15], entry_nxt [0:15];   // 4 entries/block

    // // FSM
    // reg [4:0] i;
    // always @(*) begin
    //     state_nxt = state;
    //     mode_nxt = mode;
    //     addr_nxt = addr;
    //     rdata_nxt = rdata;
    //     wdata_nxt = wdata;
    //     stall_nxt = stall;
    //     finish_nxt = finish;
    //     cen_nxt = cen;
    //     wen_nxt = wen;

    //     for (i=0; i<16; i=i+1) begin
    //         v_nxt[i] = v[i];
    //         dirty_nxt[i] = dirty[i];
    //         tag_nxt[i] = tag[i];
    //         entry_nxt[i] = entry[i];
    //     end

    //     case(state)
    //         S_IDLE: begin
    //             // $display("S_IDLE");
    //             if (i_proc_finish) begin    // write back all dirty blocks
    //                 state_nxt = S_CLEAN;
    //                 stall_nxt = 1;  // stall
    //             end 
    //             else begin
    //                 if (i_proc_cen) begin
    //                     addr_nxt = i_proc_addr;
    //                     if (i_proc_wen) begin
    //                         state_nxt = S_WRITE;
    //                         wdata_nxt = i_proc_wdata;
    //                         mode_nxt = M_WRITE;
    //                     end
    //                     else begin
    //                         state_nxt = S_READ;
    //                         mode_nxt = M_READ;
    //                     end
    //                     stall_nxt = 1;  // stall
    //                 end
    //                 else begin
    //                     state_nxt = S_IDLE; // hold
    //                     stall_nxt = 0;
    //                 end
    //             end
    //         end

    //         S_WRITE: begin
    //             // $display("S_WRITE");
    //             if (v[addr[7:4]] && (tag[addr[7:4]] == addr[31:8])) begin   // hit
    //                 for (i=0; i<16; i=i+1) begin
    //                     if (i==addr[7:4]) begin
    //                         entry_nxt[i][addr[3:2]<<<5+:BIT_W] = wdata;
    //                     end
    //                     else begin
    //                         entry_nxt[i][addr[3:2]<<<5+:BIT_W] = entry[i][addr[3:2]<<<5+:BIT_W];
    //                     end
    //                 end
    //                 state_nxt = S_IDLE;
    //                 stall_nxt = 0;
    //             end 
    //             else begin  // miss
    //                 mem_addr_nxt = {addr[31:4], 4'b0};

    //                 if (dirty[addr[7:4]]) begin // dirty
    //                     state_nxt = S_WB;
    //                     cen_nxt = 1;
    //                     wen_nxt = 1;
    //                     mem_wdata_nxt = entry[addr[7:4]];
    //                 end
    //                 else begin  // !dirty
    //                     state_nxt = S_ALLO;
    //                     cen_nxt = 1;
    //                     wen_nxt = 0;
    //                 end
    //             end
    //         end

    //         S_WB: begin
    //             // $display("S_WB");
    //             if (!i_mem_stall) begin
    //                 state_nxt =  (mode==M_CLEAN)?S_CLEAN:S_ALLO;
    //                 cen_nxt = 1;
    //                 wen_nxt = 1;
    //                 dirty_nxt[addr[7:4]] = 0;
    //             end
    //             else begin
    //                 state_nxt = S_WB;
    //                 cen_nxt = 0;
    //                 wen_nxt = 0;
    //             end
    //         end

    //         S_ALLO: begin
    //             // $display("S_ALLO");
    //             if (!i_mem_stall) begin
    //                 state_nxt  = (mode == M_READ)?S_READ:S_WRITE;
    //                 cen_nxt = 0;
    //                 wen_nxt = 0;
    //                 for (i=0; i<16; i=i+1) begin
    //                     if (i==mem_addr[7:4]) begin
    //                         entry_nxt[i] = i_mem_rdata;
    //                         tag_nxt[i] = mem_addr[31:8];
    //                         v_nxt[i] = 1;
    //                     end
    //                     else begin
    //                         entry_nxt[i] = entry[i];
    //                         tag_nxt[i] = tag[i];
    //                         v_nxt[i] = v[i];
    //                     end
    //                 end
    //             end
    //             else begin
    //                 state_nxt = S_ALLO;
    //                 cen_nxt = 0;
    //                 wen_nxt = 0;
    //             end
    //         end

    //         S_READ: begin
    //             // $display("S_READ");
    //             if (v[addr[7:4]] && (tag[addr[7:4]] == addr[31:8])) begin   // hit
    //                 rdata_nxt = entry[addr[7:4]][addr[3:2]<<<5+:BIT_W];
    //                 state_nxt = S_IDLE;
    //                 stall_nxt = 0;
    //             end 
    //             else begin  // miss
    //                 mem_addr_nxt = {addr[31:4], 4'b0};

    //                 if (dirty[addr[7:4]]) begin // dirty
    //                     state_nxt = S_WB;
    //                     cen_nxt = 1;
    //                     wen_nxt = 1;
    //                     mem_wdata_nxt = entry[addr[7:4]];
    //                 end
    //                 else begin  // !dirty
    //                     state_nxt = S_ALLO;
    //                     cen_nxt = 1;
    //                     wen_nxt = 0;
    //                 end
    //             end
    //         end

    //         S_CLEAN : begin
    //             // $display("S_CLEAN");
    //             if (dirty == 0) begin
    //                 state_nxt = S_IDLE;
    //                 finish_nxt = 1;
    //                 stall_nxt = 0;
    //             end
    //             else begin
    //                 state_nxt = S_WB;
    //                 for (i=0; i<16; i=i+1) begin
    //                     if (dirty[i]) begin
    //                         mem_addr_nxt = {tag[i], i[3:0], 4'b0};
    //                     end
    //                 end
    //                 cen_nxt = 0;
    //                 wen_nxt = 1;
    //                 mem_wdata_nxt = entry[mem_addr_nxt];
    //             end
    //         end

    //         default: begin
    //             // $display("error");
    //         end
    //     endcase
    // end

    // always @(posedge i_clk or negedge i_rst_n) begin
    //     // $display("Hi");
    //     // $display("%d", i_rst_n);
    //     // $display("%d", i_clk);
    //     if (!i_rst_n) begin
    //         state <= S_IDLE;
    //         mode <= M_READ;
    //         addr <= 0;
    //         rdata <= 0;
    //         wdata <= 0;
    //         mem_rdata <= 0;
    //         mem_wdata <= 0;
    //         mem_addr <= 0;
    //         stall <= 0;
    //         finish <= 0;
    //         cen <= 0;
    //         wen <= 0;

    //         for (i=0; i<16; i=i+1) begin
    //             v[i] <= 0;
    //             dirty[i] <= 0;
    //             tag[i] <= 0;
    //             entry [i] <= 0;
    //         end
    //     end
    //     else begin
    //         state <= state_nxt;
    //         mode <= mode_nxt;
    //         addr <= addr_nxt;
    //         rdata <= rdata_nxt;
    //         wdata <= wdata_nxt;
    //         mem_rdata <= mem_rdata_nxt;
    //         mem_wdata <= mem_wdata_nxt;
    //         mem_addr <= mem_addr_nxt;
    //         stall <= stall_nxt;
    //         finish <= finish_nxt;
    //         cen <= cen_nxt;
    //         wen <= wen_nxt;

    //         for (i=0; i<16; i=i+1) begin
    //             v[i] <= v_nxt[i];
    //             dirty[i] <= dirty_nxt[i];
    //             tag[i] <= tag_nxt[i];
    //             entry[i] <= entry_nxt[i];
    //         end
    //     end
    // end
endmodule