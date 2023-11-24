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
    parameter ecall_opcode = 7'b1110011
    parameter ecall        = 32'b0000_0000_0001_0000_0000_0000_0111_0011

    // state
    parameter S_IDLE = 5'd0
    parameter S_AUIPC = 5'd1
    parameter S_JAL = 5'd2
    parameter S_JALR = 5'd3
    parameter S_ADD = 5'd4
    parameter S_SUB = 5'd5
    parameter S_AND = 5'd6
    parameter S_XOR = 5'd7
    parameter S_ADDI = 5'd8
    parameter S_SLLI = 5'd9
    parameter S_SLTI = 5'd10
    parameter S_SRAI = 5'd11
    parameter S_LW = 5'd12
    parameter S_SW = 5'd13
    parameter S_MUL = 5'd14
    parameter S_BEQ = 5'd15
    parameter S_BGE = 5'd16
    parameter S_BLT = 5'd17
    parameter S_BNE = 5'd18
    parameter S_ECALL = 5'd19

// ------------------------------------------------------------------------------------------------------------------------------------------------------
// Wires and Registers
// ------------------------------------------------------------------------------------------------------------------------------------------------------
    
    // TODO: any declaration
    reg [4:0] state, next_state;

    // instruction memory
    reg [BIT_W-1:0] PC, next_PC;
    reg IMEM_cen, IMEM_cen_nxt;
    // wire mem_cen, mem_wen;
    // wire [BIT_W-1:0] mem_addr, mem_wdata, mem_rdata;
    // wire mem_stall;

    // register
    reg [BIT_W-1:0] imm;
    wire [BIT_W-1:0] rdata1, rdata2;
    reg [BIT_W-1:0] rdatad, rdatad_nxt;

    // data memory
    reg DMEM_cen, DMEM_cen_nxt;
    reg DMEM_wen, DMEM_wen_nxt;      
    reg [BIT_W-1:0] DMEM_addr, DMEM_addr_nxt;
    reg [BIT_W-1:0] DMEM_wdata, DMEM_wdata_nxt; 

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

    // finish procedure
    reg finish, finish_nxt;

// ------------------------------------------------------------------------------------------------------------------------------------------------------
// Continuous Assignment
// ------------------------------------------------------------------------------------------------------------------------------------------------------

    // TODO: any wire assignment

    // instruction memory
    assign o_IMEM_addr = PC;
    assign o_IMEM_cen = IMEM_cen; // load instruction

    // data memory
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

    assign o_DMEM_cen = DMEM_cen;
    assign o_DMEM_wen = DMEM_wen;
    assign o_DMEM_addr = DMEM_addr;
    assign o_DMEM_wdata = DMEM_wdata;

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
        .wdata  (rdatad),             
        .rdata1 (rdata1),           
        .rdata2 (rdata2)
    );

    MULDIV_unit muldiv0(
        .i_clk(i_clk),
        .i_rst_n(i_rst_n),
        .i_valid(state==S_MUL ? 1'b1 : 1'b0),
        .i_A(rdata1),
        .i_B(rdata2),
        .i_inst(1'b0),
        .o_data(muldiv_result),
        .o_done(muldiv_done),
    );

// ------------------------------------------------------------------------------------------------------------------------------------------------------
// Always Blocks
// ------------------------------------------------------------------------------------------------------------------------------------------------------
    
    // Todo: any combinational/sequential circuit

    // FSM

    always @(*) begin // state
        case (state)
            S_IDLE: begin
                case (i_IMEM_data[6:0])
                    auipc_opcode: begin
                        state_nxt = S_AUIPC;
                    end
                    jal_opcode: begin
                        state_nxt = S_JAL;
                    end
                    jalr_opcode: begin
                        state_nxt = S_JALR;
                    end
                    add_opcode: begin
                        case({i_IMEM_data[31:25], i_IMEM_data[14:12]})
                            {add_funct7, add_funct3}: begin
                                state_nxt = S_ADD;
                            end
                            jal_opcode: begin
                                state_nxt = S_JAL;
                            end
                            jalr_opcode: begin
                                state_nxt = S_JALR;
                            end
                            add_opcode: begin
                                case({i_IMEM_data[31:25], i_IMEM_data[14:12]})
                                    {add_funct7, add_funct3}: begin
                                        state_nxt = S_ADD;
                                    end
                                    {sub_funct7, sub_funct3}: begin
                                        state_nxt = S_SUB;
                                    end
                                    {and_funct7, and_funct3}: begin
                                        state_nxt = S_AND;
                                    end
                                    {xor_funct7, xor_functs}: begin
                                        state_nxt = S_XOR;
                                    end
                                    {mul_funct7, mul_funct3}: begin
                                        state_nxt = S_MUL;
                                    end
                                    default: begin
                                        state_nxt = state;
                                    end
                                endcase
                            end
                            addi_opcode: begin
                                case(i_IMEM_data[14:12])
                                    addi_funct3: begin
                                        state_nxt = S_ADDI;
                                    end
                                    slli_funct3: begin
                                        state_nxt = S_SLLI;
                                    end
                                    slti_funct3: begin
                                        state_nxt = S_SLTI;
                                    end
                                    srai_funct3: begin
                                        state_nxt = S_SRAI;
                                    end
                                    default: begin
                                        state_nxt = state;
                                    end
                                endcase
                            end
                            lw_opcode: begin
                                state_nxt = S_LW;
                            end
                            sw_opcode: begin
                                state_nxt = S_SW;
                            end
                            bge_opcode: begin
                                case(i_IMEM_data[6:0])
                                    bge_funct3: begin
                                        state_nxt = S_BGE;
                                    end
                                    beq_funct3: begin
                                        state_nxt = S_BEQ;
                                    end
                                    blt_funct3: begin
                                        state_nxt = S_BLT;
                                    end
                                    bne_funct3: begin
                                        state_nxt = S_BNE;
                                    end
                                    default: begin
                                        state_nxt = state;
                                    end
                                endcase
                            end
                            ecall_opcode: begin
                                state_nxt = S_ECALL;
                            end
                            default: begin
                                state_nxt = state;
                            end
                        endcase
                    end
                endcase
            end

            S_MUL: begin
                if (mul_div_done): begin
                    state_nxt = S_IDLE;
                end
                else begin
                    state_nxt = S_MUL;
                end
            end
            
            default: begin
                state_nxt = S_IDLE;
            end
        endcase
    end

    always @(*) begin // action
        imm = 0;
        rdatad_nxt = rdatad;

        case (state)
            S_IDLE: begin

            end

            S_AUIPC: begin
                imm = {i_IMEM_data[31:12], 12'b0};
                rdatad_nxt = $signed(rdata1) + $signed(imm);
            end

            S_JAL: begin
                imm = {11'b0, i_IMEM_data[31], i_IMEM_data[19:12], i_IMEM_data[20], i_IMEM_data[30:21], 1'b0};
            end

            S_JALR: begin
                imm = {20'b0, i_IMEM_data[31:20]};
            end

            S_ADD: begin
                rdatad_nxt = $signed(rdata1) + $signed(rdata2);
            end

            S_SUB: begin
            end

            S_AND: begin
            end

            S_XOR: begin
            end

            S_ADDI: begin
                imm = {20'b0, i_IMEM_data[31:20]};
            end

            S_SLLI: begin
            end

            S_SLTI: begin
                imm = {20'b0, i_IMEM_data[31:20]};
            end

            S_SRAI: begin
            end

            S_LW: begin
                imm = {20'b0, i_IMEM_data[31:20]};

            end

            S_SW: begin
                imm = {20'b0, i_IMEM_data[31:25], i_IMEM_data[12:8]};
            end

            S_MUL: begin
            end

            S_BEQ: begin
                imm = {20'b0, i_IMEM_data[31], i_IMEM_data[8], i_IMEM_data[30:25], i_IMEM_data[12:9]};
            end

            S_BGE: begin
                imm = {20'b0, i_IMEM_data[31], i_IMEM_data[8], i_IMEM_data[30:25], i_IMEM_data[12:9]};
            end

            S_BLT: begin
                imm = {20'b0, i_IMEM_data[31], i_IMEM_data[8], i_IMEM_data[30:25], i_IMEM_data[12:9]};
            end

            S_BNE: begin
                imm = {20'b0, i_IMEM_data[31], i_IMEM_data[8], i_IMEM_data[30:25], i_IMEM_data[12:9]};
            end

            S_ECALL: begin
                imm = {20'b0, i_IMEM_data[31:20]};
            end

            default: begin
                
            end
        endcase
    end

    always @(posedge i_clk or negedge i_rst_n) begin
        if (!i_rst_n) begin
            state <= S_IDLE;

            PC <= 32'h00010000; // Do not modify this value!!!
            IMEM_cen <= 1;
            
            rdatad <= 32'b0;
            DMEM_wen <= 0;
            DMEM_cen <= 1;
            DMEM_addr <= 0;
            DMEM_wdata <= 0;

            finish <= 0;
        end
        else begin
            state <= next_state;

            PC <= next_PC;
            IMEM_cen <= IMEM_cen_nxt;

            rdatad <= rdatad_nxt;
            DMEM_wen <= DMEM_wen_nxt;
            DMEM_cen <= DMEM_cen_nxt;
            DMEM_addr <= DMEM_addr_nxt;
            DMEM_wdata <= DMEM_wdata_nxt;

            finish <= finish;
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
        input [BIT_W - 1 : 0]       i_A,     // input operand A
        input [BIT_W - 1 : 0]       i_B,     // input operand B
        input                      i_inst,  // instruction

        output [2*BIT_W - 1 : 0]    o_data,  // output value
        output                      o_done   // output valid signal
    );
    // TODO: HW2
        // Do not Modify the above part !!!
// Parameters
    // ======== choose your FSM style ==========
    // 1. FSM based on operation cycles
    parameter S_IDLE           = 2'd0;
    parameter S_ONE_CYCLE_OP   = 2'd1;
    parameter S_MULTI_CYCLE_OP = 2'd2;

// Wires & Regs
    // Todo
    // state
    reg  [         1: 0] state, state_nxt; // remember to expand the bit width if you want to add more states!
    // load input
    reg  [  DATA_W-1: 0] operand_a, operand_a_nxt;
    reg  [  DATA_W-1: 0] operand_b, operand_b_nxt;
    reg  [         2: 0] inst, inst_nxt;

// Wire Assignments
    // Todo
    // Counter
    reg  [4:0] cnt, cnt_nxt;
    // Output
    reg  [2*DATA_W - 1 : 0] o_data_cur, o_data_nxt;
    reg                     o_done_cur, o_done_nxt;
    
// Always Combination
    // load input
    always @(*) begin
        if (i_valid) begin
            operand_a_nxt = i_A;
            operand_b_nxt = i_B;
            inst_nxt      = i_inst;
        end
        else begin
            operand_a_nxt = operand_a;
            operand_b_nxt = operand_b;
            inst_nxt      = inst;
        end
    end
    // Todo: FSM
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
    // Todo: Counter
    always @(negedge i_clk) begin
        if (state==S_MULTI_CYCLE_OP) begin
            cnt_nxt = cnt + 1;
        end
        else begin
            cnt_nxt = cnt;
        end
    end
    // Todo: ALU output
    always @(*) begin
        if (state==S_MULTI_CYCLE_OP) begin
            case(inst)
                1'b0: begin // MUL A: multiplicand, B: multiplier
                    if (cnt==0) begin
                        if (operand_b[0]==1)begin
                            o_data_nxt = {operand_a, operand_b} >> 1;
                        end
                        else begin
                            o_data_nxt = {{DATA_W{1'b0}}, operand_b} >> 1;
                        end
                        o_done_nxt = 0;
                    end
                    else if (cnt<31) begin
                        if (o_data_cur[0]==1) begin
                            o_data_nxt = {{1'b0, o_data_cur[2*DATA_W-1:DATA_W]} + {1'b0, operand_a}, o_data_cur[DATA_W-1:1]};
                        end
                        else begin
                            o_data_nxt = o_data_cur >> 1;
                        end
                        o_done_nxt = 0;
                    end
                    else begin
                        if (o_data_cur[0]==1) begin
                            o_data_nxt = {{1'b0, o_data_cur[2*DATA_W-1:DATA_W]} + {1'b0, operand_a}, o_data_cur[DATA_W-1:1]};
                        end
                        else begin
                            o_data_nxt = o_data_cur >> 1;
                        end
                        o_done_nxt = 1;
                    end
                end
                1'b1: begin // DIV
                    if (cnt==0) begin
                        if (operand_a[DATA_W-1] < operand_b) begin
                            o_data_nxt = operand_a << 2;
                        end
                        else begin
                            o_data_nxt = (({{(DATA_W-1){1'b0}}, operand_a, 1'b0}-{operand_b, {DATA_W{1'b0}}}) << 1) + 1;
                        end
                        o_done_nxt = 0;
                    end
                    else if (cnt<31) begin
                        if (o_data_cur[2*DATA_W-1:DATA_W] < operand_b) begin // shift_l
                            o_data_nxt = o_data_cur << 1;
                        end
                        else begin // // sub, shift_l
                            o_data_nxt[2*DATA_W-1:DATA_W+1] = o_data_cur[2*DATA_W-1:DATA_W]-operand_b;
                            o_data_nxt[DATA_W:0] = (o_data_cur[DATA_W-1:0] << 1) + 1;
                        end
                        o_done_nxt = 0;
                    end
                    else begin // cnt==31
                        if (o_data_cur[2*DATA_W-1:DATA_W] < operand_b) begin // shift_l, shift_r(left_half)
                            o_data_nxt[2*DATA_W-1:DATA_W] = o_data_cur[2*DATA_W-1:DATA_W];
                            o_data_nxt[DATA_W-1:0] = o_data_cur[DATA_W-1:0] << 1;
                        end
                        else begin // sub, shift_l, shift_r(left_half)
                            o_data_nxt[2*DATA_W-1:DATA_W] = o_data_cur[2*DATA_W-1:DATA_W] - operand_b;
                            o_data_nxt[DATA_W-1:0] = (o_data_cur[DATA_W-1:0] << 1) + 1;
                        end
                        o_done_nxt = 1;
                    end
                end
                default: begin
                    o_data_nxt = o_data_cur;
                    o_done_nxt = o_done_cur;
                end
            endcase
        end
        else begin
            o_data_nxt = 0;
            o_done_nxt = 0;
        end
    end
    
    // Todo: output valid signal
    assign o_data = o_data_cur;
    assign o_done = o_done_cur;

    // Todo: Sequential always block
    always @(posedge i_clk or negedge i_rst_n) begin
        if (!i_rst_n) begin
            state       <= S_IDLE;
            operand_a   <= 0;
            operand_b   <= 0;
            inst        <= 0;
            cnt         <= 0;
            o_data_cur  <= 0;
            o_done_cur  <= 0;
        end
        else begin
            state       <= state_nxt;
            operand_a   <= operand_a_nxt;
            operand_b   <= operand_b_nxt;
            inst        <= inst_nxt;
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

    // TODO: BONUS

endmodule