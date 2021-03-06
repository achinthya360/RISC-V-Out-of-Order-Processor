`timescale 1ns/1ns

module top(inst1_FD, inst2_FD);
	// self clocking for simulation
	reg clk;
	reg [31:0] pc; 
	integer cyclecount;

	// OUTPUTS OF FETCH
	output reg [31:0] inst1_FD, inst2_FD; // instructions from FETCH to DECODE module (pipeline registers)
	reg [31:0] pc_F; // PC for FETCH module
	wire done; // FETCH tells us once 10 empty instructions have been read in

	// PIPELINE REGISTERS BETWEEN FETCH AND DECODE
	reg [31:0] inst1_FtoD, inst2_FtoD; 

	// OUTPUTS OF DECODE
	reg [4:0] rs2_1_DR, rs1_1_DR, rd_1_DR, rs2_2_DR, rs1_2_DR, rd_2_DR;
	reg [31:0] imm_1_DR, imm_2_DR;
	reg MemRead_1_DR, MemtoReg_1_DR, MemWrite_1_DR, ALUSrc_1_DR /* 0: rs2, 1: imm */, RegWrite_1_DR; 
	reg MemRead_2_DR, MemtoReg_2_DR, MemWrite_2_DR, ALUSrc_2_DR /* 0: rs2, 1: imm */, RegWrite_2_DR;  
	reg [1:0] ALUOp_1_DR, ALUOp_2_DR; // 00: ADD, 01: SUB, 10: OR, 11: AND
	
	// PIPELINE REGISTERS BETWEEN DECODE AND RENAME
	reg [4:0] rs2_1_DtoR, rs1_1_DtoR, rd_1_DtoR, rs2_2_DtoR, rs1_2_DtoR, rd_2_DtoR;
	reg [31:0] imm_1_DtoR, imm_2_DtoR;
	reg MemRead_1_DtoR, MemtoReg_1_DtoR, MemWrite_1_DtoR, ALUSrc_1_DtoR /* 0: rs2, 1: imm */, RegWrite_1_DtoR; 
	reg MemRead_2_DtoR, MemtoReg_2_DtoR, MemWrite_2_DtoR, ALUSrc_2_DtoR /* 0: rs2, 1: imm */, RegWrite_2_DtoR;  
	reg [1:0] ALUOp_1_DtoR, ALUOp_2_DtoR; // 00: ADD, 01: SUB, 10: OR, 11: AND
	reg [31:0] PC_DtoR1, PC_DtoR2; // PC to send to ROB in DISPATCH stage
	
	// OUTPUTS OF RENAME
	reg [6:0] rs1_1_RDI, rs2_1_RDI, rd_1_RDI, rs1_2_RDI, rs2_2_RDI, rd_2_RDI, olddest_1_RDI, olddest_2_RDI; // physical registers after renaming
	reg [31:0] PC_RDi1, PC_RDi2; // PC to send to ROB in DISPATCH stage

	// PIPELINE REGISTER BETWEEN RENAME AND DISPATCH
	reg [6:0] rs1_1_RtoDI, rs2_1_RtoDI, rd_1_RtoDI, rs1_2_RtoDI, rs2_2_RtoDI, rd_2_RtoDI, olddest_1_RtoDI, olddest_2_RtoDI;
	reg [31:0] imm_1_RtoDI, imm_2_RtoDI; 
	reg MemRead_1_RtoDI, MemtoReg_1_RtoDI, MemWrite_1_RtoDI, ALUSrc_1_RtoDI /* 0: rs2, 1: imm */, RegWrite_1_RtoDI; 
	reg MemRead_2_RtoDI, MemtoReg_2_RtoDI, MemWrite_2_RtoDI, ALUSrc_2_RtoDI /* 0: rs2, 1: imm */, RegWrite_2_RtoDI;  
	reg [1:0] ALUOp_1_RtoDI, ALUOp_2_RtoDI; // 00: ADD, 01: SUB, 10: OR, 11: AND
	reg [31:0] PC_RtoDI1, PC_RtoDI2; // PC to send to ROB in DISPATCH stage
	
	// communication between RENAME AND EXECUTE for free pool freeing
	wire [6:0] regtofree_1, regtofree_2;
	
	initial begin
		clk = 0;
		pc = 0;
		cyclecount = 0;
	end

	// stage initializations
	// FETCH
	fetch F(.clk(clk), .pc(pc_F), .inst1(inst1_FD), .inst2(inst2_FD), .done(done));
	// DECODE
	decode D(.inst1(inst1_FD), .inst2(inst2_FD), 
	.rs2_1(rs2_1_DR), .rs1_1(rs1_1_DR), .rd_1(rd_1_DR), .imm_1(imm_1_DR), 
	.rs2_2(rs2_2_DR), .rs1_2(rs1_2_DR), .rd_2(rd_2_DR), .imm_2(imm_2_DR), 

	.MemRead_1(MemRead_1_DR), .MemtoReg_1(MemtoReg_1_DR), .MemWrite_1(MemWrite_1_DR), .ALUSrc_1(ALUSrc_1_DR), .RegWrite_1(RegWrite_1_DR), .ALUOp_1(ALUOp_1_DR), 
	.MemRead_2(MemRead_2_DR), .MemtoReg_2(MemtoReg_2_DR), .MemWrite_2(MemWrite_2_DR), .ALUSrc_2(ALUSrc_2_DR), .RegWrite_2(RegWrite_2_DR), .ALUOp_2(ALUOp_2_DR)
	);
	// RENAME
	rename R(.rs1_1(rs1_1_DtoR), .rs2_1(rs2_1_DtoR), .rd_1(rd_1_DtoR), .rs1_2(rs1_2_DtoR), .rs2_2(rs2_2_DtoR), .rd_2(rd_2_DtoR), 
		.rs1out_1(rs1_1_RDI), .rs2out_1(rs2_1_RDI), .rdout_1(rd_1_RDI),
		.rs1out_2(rs1_2_RDI), .rs2out_2(rs2_2_RDI), .rdout_2(rd_2_RDI),
		.olddest_1(olddest_1_RDI), .olddest_2(olddest_2_RDI),
		.RegWrite_1(RegWrite_1_DtoR), .RegWrite_2(RegWrite_2_DtoR), .MemWrite_1(MemWrite_1_DtoR), .MemWrite_2(MemWrite_2_DtoR), .ALUSrc_1(ALUSrc_1_DtoR), .ALUSrc_2(ALUSrc_2_DtoR),
		.freereg_1(regtofree_1), .freereg_2(regtofree_2));

	// DISPATCH, ISSUE, COMPLETE, RETIRE
	execute E(.clk(clk), .rs1_1(rs1_1_RtoDI), .rs2_1(rs2_1_RtoDI), .rd_1(rd_1_RtoDI), .rs1_2(rs1_2_RtoDI), .rs2_2(rs2_2_RtoDI), .rd_2(rd_2_RtoDI),
		.olddest_1(olddest_1_RtoDI), .olddest_2(olddest_2_RtoDI), .imm_1(imm_1_RtoDI), .imm_2(imm_2_RtoDI), 
		.MemRead_1(MemRead_1_RtoDI), .MemtoReg_1(MemtoReg_1_RtoDI), .MemWrite_1(MemWrite_1_RtoDI), .ALUSrc_1(ALUSrc_1_RtoDI), .RegWrite_1(RegWrite_1_RtoDI),
		.MemRead_2(MemRead_2_RtoDI), .MemtoReg_2(MemtoReg_2_RtoDI), .MemWrite_2(MemWrite_2_RtoDI), .ALUSrc_2(ALUSrc_2_RtoDI), .RegWrite_2(RegWrite_2_RtoDI),
		.ALUOp_1(ALUOp_1_RtoDI), .ALUOp_2(ALUOp_2_RtoDI),
		.freereg_1(regtofree_1), .freereg_2(regtofree_2),
		.PC_R1(PC_RtoDI1), .PC_R2(PC_RtoDI2));
	
	always @(posedge clk) begin
		if(pc >= 0) begin
			/* FETCH debugging
			$display("Fetched [1] instruction 0x%2h: %b, %b, %b, %b", pc-8, inst1_FD[31:24], inst1_FD[23:16], inst1_FD[15:8], inst1_FD[7:0]);
			$display("rs1: %d, rs2: %d, rd: %d", rs1_1_DR, rs2_1_DR, rd_1_DR);
			$display("Fetched [2] instruction 0x%2h: %b, %b, %b, %b", pc-4, inst2_FD[31:24], inst2_FD[23:16], inst2_FD[15:8], inst2_FD[7:0]);
			$display("rs1: %d, rs2: %d, rd: %d", rs1_2_DR, rs2_2_DR, rd_2_DR);
			*/
			// INCREMENT PC
			pc <= pc + 8;

			// INPUT PC TO FETCH
			pc_F <= pc; 
	
			// PUSH PIPELINE FETCH TO DECODE
			PC_DtoR1 <= pc_F;
			PC_DtoR2 <= pc_F+4;
			inst1_FtoD <= inst1_FD;
			inst2_FtoD <= inst2_FD;

			// PUSH PIPELINE DECODE TO RENAME
			PC_RDi1 <= PC_DtoR1;
			PC_RDi2 <= PC_DtoR2;
			rs2_1_DtoR <= rs2_1_DR;
			rs1_1_DtoR <= rs1_1_DR;
			rd_1_DtoR  <= rd_1_DR;
			rs2_2_DtoR <= rs2_2_DR;
			rs1_2_DtoR <= rs1_2_DR;
			rd_2_DtoR <= rd_2_DR;
			imm_1_DtoR <= imm_1_DR;
			imm_2_DtoR <= imm_2_DR;
			MemRead_1_DtoR <= MemRead_1_DR;
			MemtoReg_1_DtoR <= MemtoReg_1_DR;
			MemWrite_1_DtoR <= MemWrite_1_DR;
			ALUSrc_1_DtoR <= ALUSrc_1_DR;
			RegWrite_1_DtoR <= RegWrite_1_DR; 
			MemRead_2_DtoR <= MemRead_2_DR;
			MemtoReg_2_DtoR <= MemtoReg_2_DR;
			MemWrite_2_DtoR <= MemWrite_2_DR;
			ALUSrc_2_DtoR <= ALUSrc_2_DR;
			RegWrite_2_DtoR <= RegWrite_2_DR;
			ALUOp_1_DtoR <= ALUOp_1_DR;
			ALUOp_2_DtoR <= ALUOp_2_DR;

			// PUSH PIPELINE RENAME TO DISPATCH
			PC_RtoDI1 <= PC_RDi1;
			PC_RtoDI2 <= PC_RDi2;
			rs1_1_RtoDI <= rs1_1_RDI;
			rs2_1_RtoDI <= rs2_1_RDI;
			rd_1_RtoDI <= rd_1_RDI;
			rs1_2_RtoDI <= rs1_2_RDI;
			rs2_2_RtoDI <= rs2_2_RDI;
			rd_2_RtoDI <= rd_2_RDI;
			olddest_1_RtoDI <= olddest_1_RDI;
			olddest_2_RtoDI <= olddest_2_RDI;
			imm_1_RtoDI <= imm_1_DtoR;
			imm_2_RtoDI <= imm_2_DtoR;
			MemRead_1_RtoDI <= MemRead_1_DtoR;
			MemtoReg_1_RtoDI <= MemtoReg_1_DtoR;
			MemWrite_1_RtoDI <= MemWrite_1_DtoR;
			ALUSrc_1_RtoDI <= ALUSrc_1_DtoR;
			RegWrite_1_RtoDI <= RegWrite_1_DtoR; 
			MemRead_2_RtoDI <= MemRead_2_DtoR;
			MemtoReg_2_RtoDI <= MemtoReg_2_DtoR;
			MemWrite_2_RtoDI <= MemWrite_2_DtoR;
			ALUSrc_2_RtoDI <= ALUSrc_2_DtoR;
			RegWrite_2_RtoDI <= RegWrite_2_DtoR;
			ALUOp_1_RtoDI <= ALUOp_1_DtoR;
			ALUOp_2_RtoDI <= ALUOp_2_DtoR;
		end
		if(done) begin
			$stop();
		end
	end
	
	always begin
		#1
		clk = ~clk;
	end
	
	always @(negedge clk) begin
		$display("Cycle: %d", cyclecount);
		cyclecount++;
	end

endmodule
