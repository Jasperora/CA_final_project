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
    
    // TODO: any declaration

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
    reg DMEM_cen, DMEM_cen_nxt;
    reg DMEM_wen, DMEM_wen_nxt;
    reg DMEM_ready, DMEM_ready_nxt;

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
    reg muldiv_ready, muldiv_ready_nxt;

    // finish procedure
    reg finish, finish_nxt;

// ------------------------------------------------------------------------------------------------------------------------------------------------------
// Continuous Assignment
// ------------------------------------------------------------------------------------------------------------------------------------------------------

    // TODO: any wire assignment

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
    assign o_DMEM_cen = MemtoReg || ((MemRead || MemWrite) && DMEM_cen);
    assign o_DMEM_wen = MemWrite && DMEM_wen;
    assign o_DMEM_addr = DMEM_addr_nxt;
    assign o_DMEM_wdata = DMEM_wdata;

    // finish
    // assign o_finish = finish; // without cache
    assign o_proc_finish = finish;
    assign o_finish = i_cache_finish;

// ------------------------------------------------------------------------------------------------------------------------------------------------------
// Submoddules
// ------------------------------------ ------------------------------------------------------------------------------------------------------------------

    // TODO: Reg_file wire connection
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
        .i_valid(muldiv_valid_nxt),
        .i_A(rdata1),
        .i_B(rdata2),
        .o_data(muldiv_result),
        .o_done(muldiv_done)
    );

// ------------------------------------------------------------------------------------------------------------------------------------------------------
// Always Blocks
// ------------------------------------------------------------------------------------------------------------------------------------------------------
    // Todo: any combinational/sequential circuit

    // action given instructions
    always @(*) begin
        // default assignments
        muldiv_ready_nxt = 1;
        DMEM_ready_nxt = 1;
        muldiv_valid_nxt = 0;
        DMEM_cen_nxt = 1;
        DMEM_wen_nxt = 1;

        PC_nxt = PC;

        rdatad_nxt = rdatad;
        DMEM_addr_nxt = DMEM_addr;
        DMEM_wdata_nxt = DMEM_wdata;
        DMEM_rdata_nxt = DMEM_rdata;

        finish_nxt = finish;

        // ombinational circuit
        case (i_IMEM_data[6:0])
            auipc_opcode: begin
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
                imm = {{20{i_IMEM_data[31]}}, i_IMEM_data[31:20]};
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
                        PC_nxt = muldiv_done ? ($signed(PC) + $signed(4)) : PC;
                        muldiv_ready_nxt = muldiv_done ? 1 : 0;
                        muldiv_valid_nxt = muldiv_ready;
                        rdatad_nxt = muldiv_done ? muldiv_result : rdatad;
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
                        imm = {{20{i_IMEM_data[31]}}, i_IMEM_data[31:20]};
                        rdatad_nxt = $signed(rdata1) + $signed(imm);
                        PC_nxt = $signed(PC) + $signed(4);
                    end
                    slli_funct3: begin
                        // slli
                        imm = i_IMEM_data[24:20];
                        rdatad_nxt = rdata1 << imm;
                        PC_nxt = $signed(PC) + $signed(4);
                    end
                    slti_funct3: begin
                        // slti
                        imm = {{20{i_IMEM_data[31]}}, i_IMEM_data[31:20]};
                        rdatad_nxt = (rdata1 < imm) ? 1 : 0;
                        PC_nxt = $signed(PC) + $signed(4);
                    end
                    srai_funct3: begin
                        // srai
                        imm = i_IMEM_data[24:20];
                        rdatad_nxt = $signed(rdata1) >>> imm;
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
                if (i_DMEM_stall) begin
                    imm = {{20{i_IMEM_data[31]}}, i_IMEM_data[31:20]};
                    DMEM_addr_nxt = $signed(rdata1) + $signed(imm);
                    rdatad_nxt = rdatad;
                    PC_nxt = PC;
                    DMEM_ready_nxt = 0;
                    DMEM_cen_nxt = DMEM_ready;
                end
                else begin
                    imm = {{20{i_IMEM_data[31]}}, i_IMEM_data[31:20]};
                    DMEM_addr_nxt = $signed(rdata1) + $signed(imm);
                    rdatad_nxt = i_DMEM_rdata;
                    PC_nxt = $signed(PC) + $signed(4);
                    DMEM_cen_nxt = 1;
                    DMEM_ready_nxt = 1;
                end
            end
            sw_opcode: begin
                // sw
                if (i_DMEM_stall) begin
                    imm = {{20{i_IMEM_data[31]}}, i_IMEM_data[31:25], i_IMEM_data[11:7]};
                    DMEM_addr_nxt = rdata1 + imm;
                    DMEM_wdata_nxt = rdata2;
                    PC_nxt = PC;
                    DMEM_ready_nxt = 0;
                    DMEM_cen_nxt = DMEM_ready;
                    DMEM_wen_nxt = DMEM_ready;
                end
                else begin
                    DMEM_addr_nxt = DMEM_addr;
                    DMEM_wdata_nxt = DMEM_wdata;
                    PC_nxt = $signed(PC) + $signed(4);
                    DMEM_cen_nxt = 1;
                    DMEM_ready_nxt = 1;
                    DMEM_wen_nxt = 1;
                end
            end
            bge_opcode: begin
                case(i_IMEM_data[14:12])
                    bge_funct3: begin
                        // bge
                        imm = {{20{i_IMEM_data[31]}}, i_IMEM_data[31], i_IMEM_data[7], i_IMEM_data[30:25], i_IMEM_data[11:8]};
                        PC_nxt = ($signed(rdata1) >= $signed(rdata2)) ? ($signed(PC) + $signed({imm, 1'b0})) : $signed(PC) + $signed(4);
                    end
                    beq_funct3: begin
                        // beq
                        imm = {{20{i_IMEM_data[31]}}, i_IMEM_data[31], i_IMEM_data[7], i_IMEM_data[30:25], i_IMEM_data[11:8]};
                        PC_nxt = ($signed(rdata1) == $signed(rdata2)) ? ($signed(PC) + $signed({imm, 1'b0})) : $signed(PC) + $signed(4);
                    end
                    blt_funct3: begin
                        // blt
                        imm = {{20{i_IMEM_data[31]}}, i_IMEM_data[31], i_IMEM_data[7], i_IMEM_data[30:25], i_IMEM_data[11:8]};
                        PC_nxt = ($signed(rdata1) < $signed(rdata2)) ? ($signed(PC) + $signed({imm, 1'b0})) : $signed(PC) + $signed(4);
                    end
                    bne_funct3: begin
                        // bne
                        imm = {{20{i_IMEM_data[31]}}, i_IMEM_data[31], i_IMEM_data[7], i_IMEM_data[30:25], i_IMEM_data[11:8]};
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
        if (!i_rst_n) begin
            PC <= 32'h00010000; // Do not modify this value!!!
            
            rdatad <= 32'b0;
            DMEM_addr <= 0;
            DMEM_wdata <= 0;
            DMEM_rdata <= 0;

            finish <= 0;
            muldiv_valid <= 0;
            muldiv_ready <= 0;
            DMEM_ready <= 1;
            DMEM_cen <= 0;
            DMEM_wen <= 0;
        end
        else begin
            PC <= PC_nxt;

            rdatad <= rdatad_nxt;
            DMEM_addr <= DMEM_addr_nxt;
            DMEM_wdata <= DMEM_wdata_nxt;
            DMEM_rdata <= DMEM_rdata_nxt;

            finish <= finish_nxt;
            muldiv_valid <= muldiv_valid_nxt;
            muldiv_ready <= muldiv_ready_nxt;
            DMEM_ready <= DMEM_ready_nxt;
            DMEM_cen <= DMEM_cen_nxt;
            DMEM_wen <= DMEM_wen_nxt;
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
        input                       i_clk,   // clock
        input                       i_rst_n, // reset

        input                       i_valid, // input valid signal
        input [BIT_W - 1 : 0]       i_A,     // input operand A
        input [BIT_W - 1 : 0]       i_B,     // input operand B

        output [BIT_W - 1 : 0]    o_data,  // output value
        output                      o_done   // output valid signal
    );
    // Do not Modify the above part !!!
    
    // Parameters
    parameter S_IDLE           = 2'd0;
    parameter S_MULTI_CYCLE_OP = 2'd2;

    // Wires & Regs
    // state
    reg  [1:0]  state, state_nxt; // remember to expand the bit width if you want to add more states!
    // load input
    reg  [BIT_W-1:0]   operand_a, operand_a_nxt;
    reg  [BIT_W-1:0]   operand_b, operand_b_nxt;
    reg  [2:0]  inst, inst_nxt;

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
    assign o_data = o_data_cur[BIT_W-1:0];
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

module Cache#(  // 545 -> 535
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

    assign o_cache_available = 1; // change this value to 1 if the cache is implemented

    //------------------------------------------//
    //          default connection              //
    // assign o_mem_cen = i_proc_cen;              //
    // assign o_mem_wen = i_proc_wen;              //
    // assign o_mem_addr = i_proc_addr;            //
    // assign o_mem_wdata = i_proc_wdata;          //
    // assign o_proc_rdata = i_mem_rdata[0+:BIT_W];//
    // assign o_proc_stall = i_mem_stall;          //
    //------------------------------------------//

    // registers
    reg [2:0] state, state_nxt;
    reg [1:0] mode, mode_nxt;
    
    // data/address
    reg [ADDR_W-1:0] addr, addr_nxt;
    reg [ADDR_W-1:0] real_addr, real_addr_nxt;
    reg [BIT_W-1:0] rdata, rdata_nxt;
    reg [BIT_W-1:0]  wdata, wdata_nxt;
    reg [ADDR_W-1:0] mem_addr, mem_addr_nxt;
    reg [BIT_W*4-1:0]  mem_wdata, mem_wdata_nxt;
    wire [BIT_W-1:0] rdata_out;
    wire hit, hit_idx, miss_idx, clean_idx;
    reg entry_dirty;
    // control signals
    reg stall, stall_nxt;
    reg finish, finish_nxt;
    reg cen, cen_nxt;
    reg wen, wen_nxt;

    // parameters
    // state
    parameter S_IDLE    = 3'd0;
    parameter S_READ_WRITE   = 3'd1;
    parameter S_WB      = 3'd2;
    parameter S_ALLO    = 3'd3;
    parameter S_CLEAN   = 3'd4; // write baack all dirty blocks when i_proc_finish=1
    // mode
    parameter M_IDLE    = 2'd0;
    parameter M_READ    = 2'd1;
    parameter M_WRITE   = 2'd2;
    parameter M_CLEAN   = 2'd3;
    

    // entries
    reg [0:1] v[0:7], v_nxt[0:7]; // valid bit
    reg [0:1] dirty[0:7], dirty_nxt[0:7];  // dirty bit
    reg [0:7] new, new_nxt;  // tag the currently used block
    reg [31:7] tag [0:7][0:1], tag_nxt [0:7][0:1];
    reg [BIT_W*4-1:0] entry [0:7][0:1], entry_nxt [0:7][0:1];   // 4 entries/block, 2-way associated

    // processor
    assign o_proc_rdata = rdata_out;
    assign o_proc_stall = stall?(state_nxt!=S_IDLE): i_proc_cen;
    assign o_cache_finish = finish;
    // memory
    assign rdata_out = (state==S_ALLO || (state==S_READ_WRITE && mode == M_READ))?rdata_nxt:32'b0;
    assign o_mem_cen = cen;
    assign o_mem_wen = wen;
    assign o_mem_addr = i_offset + {(mem_addr-i_offset)>>4, 4'b0};
    assign o_mem_wdata = mem_wdata;
    assign hit = (v[real_addr[6:4]][0] && (tag[real_addr[6:4]][0] == real_addr[31:7])) || (v[real_addr[6:4]][1] && (tag[real_addr[6:4]][1] == real_addr[31:7]));
    assign hit_idx = (tag[real_addr[6:4]][0] == real_addr[31:7])?0:1;
    assign miss_idx = new[real_addr[6:4]]?0:1;
    assign clean_idx = (real_addr_nxt[31:7]==tag[real_addr_nxt[6:4]][0])?0:1;

    // FSM
    reg [3:0] i;
    reg [2:0] j;
    always @(*) begin
        // default assignments
        state_nxt = state;
        mode_nxt = mode;
        addr_nxt = addr;
        rdata_nxt = rdata;
        wdata_nxt = wdata;
        mem_wdata_nxt = mem_wdata;
        mem_addr_nxt = mem_addr;
        real_addr_nxt = real_addr;
        stall_nxt = stall;
        finish_nxt = finish;
        cen_nxt = cen;
        wen_nxt = wen;

        for (i=0; i<8; i=i+1) begin
            new_nxt[i] = new[i];
            for (j=0; j<2; j=j+1) begin
                v_nxt[i][j] = v[i][j];
                dirty_nxt[i][j] = dirty[i][j];
                tag_nxt[i][j] = tag[i][j];
                entry_nxt[i][j] = entry[i][j];
            end
        end

        case(state)
            S_IDLE: begin
                cen_nxt = 0;
                wen_nxt = 0;

                rdata_nxt = 32'b0;
                wdata_nxt = 32'b0;
                mem_wdata_nxt = 128'b0;

                if (i_proc_finish) begin    // write back all dirty blocks
                    state_nxt = S_CLEAN;
                    mode_nxt = M_CLEAN;
                    stall_nxt = 1;  // stall
                end 
                else begin
                    addr_nxt = i_proc_addr;
                    mem_addr_nxt = i_proc_addr;
                    real_addr_nxt = i_proc_addr-i_offset;   // used for cache addressing
                    if (i_proc_cen) begin
                        if (i_proc_wen) begin   // write
                            state_nxt = S_READ_WRITE;
                            mode_nxt = M_WRITE;
                        end
                        else begin  // read
                            state_nxt = S_READ_WRITE;
                            mode_nxt = M_READ;
                        end
                        stall_nxt = 1;  // stall
                    end
                    else begin
                        state_nxt = S_IDLE; // hold
                        mode_nxt = M_IDLE;
                        stall_nxt = 0;
                    end
                end
            end

            S_READ_WRITE: begin

                if (hit) begin   // hit
                    state_nxt = S_IDLE;
                    stall_nxt = 0;
                    new_nxt[real_addr[6:4]] = hit_idx;  // marked "currently used" iif accessed

                    if (mode == M_WRITE) begin  // write
                        wdata_nxt = 32'b0;

                        for (i=0; i<8; i=i+1) begin
                            for (j=0; j<2; j=j+1) begin
                                if (i==real_addr[6:4]) begin
                                    dirty_nxt[i][hit_idx] = 1;
                                    case (real_addr[3:2])
                                        0: entry_nxt[i][hit_idx] = {entry[i][hit_idx][4*BIT_W-1:1*BIT_W], i_proc_wdata};
                                        1: entry_nxt[i][hit_idx] = {entry[i][hit_idx][4*BIT_W-1:2*BIT_W], i_proc_wdata, entry[i][hit_idx][1*BIT_W-1:0]};
                                        2: entry_nxt[i][hit_idx] = {entry[i][hit_idx][4*BIT_W-1:3*BIT_W], i_proc_wdata, entry[i][hit_idx][2*BIT_W-1:0]};
                                        3: entry_nxt[i][hit_idx] = {i_proc_wdata, entry[i][hit_idx][3*BIT_W-1:0]};
                                    endcase
                                end
                                else begin
                                    entry_nxt[i][j] = entry[i][j];
                                end
                            end
                        end
                    end else begin  // read
                        rdata_nxt = entry[real_addr[6:4]][hit_idx][{real_addr[3:2], 5'b0}+:BIT_W];
                    end
                end 
                else begin  // miss
                    wdata_nxt = i_proc_wdata;

                    if (dirty[real_addr[6:4]][miss_idx]) begin // dirty
                        state_nxt = S_WB;
                        cen_nxt = 1;
                        wen_nxt = 1;
                        mem_addr_nxt = {tag[real_addr[6:4]][miss_idx], real_addr[6:4], 4'b0} + i_offset;
                        mem_wdata_nxt = entry[real_addr[6:4]][miss_idx];
                    end
                    else begin  // !dirty
                        state_nxt = S_ALLO;
                        cen_nxt = 1;
                        wen_nxt = 0;
                        mem_wdata_nxt = wdata;
                    end
                end
            end

            S_WB: begin
                if (!i_mem_stall) begin
                    state_nxt = (mode==M_CLEAN)?S_CLEAN:S_ALLO;
                    dirty_nxt[real_addr[6:4]][(mode==M_CLEAN)?clean_idx:miss_idx] = 0;
                    cen_nxt = (mode==M_CLEAN)?0:1;
                    wen_nxt = 0;
                    mem_addr_nxt = addr;
                end
                else begin  // DMEM stall
                    state_nxt = S_WB;
                    cen_nxt = 0;
                    wen_nxt = 0;
                end
            end

            S_ALLO: begin
                cen_nxt = 0;
                wen_nxt = 0;

                if (!i_mem_stall) begin
                    state_nxt = S_IDLE;
                    rdata_nxt = (mode==M_READ)?i_mem_rdata[{real_addr[3:2], 5'b0}+:BIT_W]:32'b0;
                    new_nxt[real_addr[6:4]] = miss_idx;  // marked "currently used" if accessed


                    for (i=0; i<8; i=i+1) begin
                        for (j=0; j<2; j=j+1) begin
                            if (i==real_addr[6:4]) begin
                                tag_nxt[i][miss_idx] = real_addr[31:7];
                                v_nxt[i][miss_idx] = 1;
                                
                                if (mode==M_WRITE) begin    // write
                                    dirty_nxt[i][miss_idx] = 1;
                                    case (real_addr[3:2])
                                        0: entry_nxt[i][miss_idx] = {i_mem_rdata[4*BIT_W-1:1*BIT_W], wdata};
                                        1: entry_nxt[i][miss_idx] = {i_mem_rdata[4*BIT_W-1:2*BIT_W], wdata, i_mem_rdata[1*BIT_W-1:0]};
                                        2: entry_nxt[i][miss_idx] = {i_mem_rdata[4*BIT_W-1:3*BIT_W], wdata, i_mem_rdata[2*BIT_W-1:0]};
                                        3: entry_nxt[i][miss_idx] = {wdata, i_mem_rdata[3*BIT_W-1:0]};
                                    endcase
                                end else begin  // read
                                    entry_nxt[i][j] = i_mem_rdata;
                                end
                            end
                            else begin
                                entry_nxt[i][j] = entry[i][j];
                                tag_nxt[i][j] = tag[i][j];
                                v_nxt[i][j] = v[i][j];
                            end
                        end
                    end
                end
                else begin  // DMEM stall
                    state_nxt = S_ALLO;
                    cen_nxt = 0;
                    wen_nxt = 0;
                end
            end

            S_CLEAN : begin
                mode_nxt = M_CLEAN;
                
                entry_dirty = 0;
                for (i=0; i<8; i=i+1) begin
                    for (j=0; j<2; j=j+1) begin
                        if (dirty[i][j]) entry_dirty = 1;
                    end
                end

                if (!entry_dirty) begin
                    cen_nxt = 0;
                    wen_nxt = 0;

                    state_nxt = S_IDLE;
                    finish_nxt = 1;
                    stall_nxt = 0;
                end
                else begin
                    state_nxt = S_WB;
                    cen_nxt = 1;
                    wen_nxt = 1;

                    for (i=0; i<8; i=i+1) begin
                        for (j=0; j<2; j=j+1) begin
                            if (dirty[i][j]) begin
                                real_addr_nxt = {tag[i][j], i[2:0], 4'b0};
                            end
                        end
                    end

                    mem_addr_nxt = real_addr_nxt + i_offset;
                    mem_wdata_nxt = entry[real_addr_nxt[6:4]][clean_idx];
                end
            end

            default: begin
            end
        endcase
    end

    always @(posedge i_clk or negedge i_rst_n) begin
        if (!i_rst_n) begin
            state <= S_IDLE;
            mode <= M_READ;
            addr <= i_offset;
            rdata <= 0;
            wdata <= 0;
            mem_wdata <= 0;
            mem_addr <= i_offset;
            real_addr <= 0;
            stall <= 0;
            finish <= 0;
            cen <= 0;
            wen <= 0;

            for (i=0; i<8; i=i+1) begin
                new[i] <= 1;

                for (j=0; j<2; j=j+1) begin
                    v[i][j] <= 0;
                    dirty[i][j] <= 0;
                    tag[i][j] <= 0;
                    entry [i][j] <= 0;
                end
            end
        end
        else begin
            state <= state_nxt;
            mode <= mode_nxt;
            addr <= addr_nxt;
            rdata <= rdata_nxt;
            wdata <= wdata_nxt;
            mem_wdata <= mem_wdata_nxt;
            mem_addr <= mem_addr_nxt;
            real_addr <= real_addr_nxt;
            stall <= stall_nxt;
            finish <= finish_nxt;
            cen <= cen_nxt;
            wen <= wen_nxt;

            for (i=0; i<8; i=i+1) begin
                new[i] <= new_nxt[i];

                for (j=0; j<2; j=j+1) begin
                    v[i][j] <= v_nxt[i][j];
                    dirty[i][j] <= dirty_nxt[i][j];
                    tag[i][j] <= tag_nxt[i][j];
                    entry[i][j] <= entry_nxt[i][j];
                end
            end
        end
    end
endmodule