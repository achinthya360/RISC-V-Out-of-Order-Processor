module decode(
	inst1, inst2, 
	
	rs2_1, rs1_1, rd_1, imm_1, 
	rs2_2, rs1_2, rd_2, imm_2, 

	MemRead_1, MemtoReg_1, MemWrite_1, ALUSrc_1, RegWrite_1, ALUOp_1, 
	MemRead_2, MemtoReg_2, MemWrite_2, ALUSrc_2, RegWrite_2, ALUOp_2
	);
	input [31:0] inst1, inst2;

	output [4:0] rs2_1, rs1_1, rd_1, rs2_2, rs1_2, rd_2;
	wire [6:0] funct7_1, opcode_1, funct7_2, opcode_2;
	wire [2:0] funct3_1, funct3_2;
	output [31:0] imm_1, imm_2;

	output MemRead_1, MemtoReg_1, MemWrite_1, ALUSrc_1 /* 0: rs2, 1: imm */, RegWrite_1; 
	output MemRead_2, MemtoReg_2, MemWrite_2, ALUSrc_2 /* 0: rs2, 1: imm */, RegWrite_2;  
	output reg [1:0] ALUOp_1, ALUOp_2; // 00: ADD, 01: SUB, 10: OR, 11: AND

	// extract bit sequences from instruction 1
	assign funct7_1 = inst1[31:25];
	assign rs2_1 = inst1[24:20];
	assign rs1_1 = inst1[19:15];
	assign funct3_1 = inst1[14:12];
	assign opcode_1 = inst1[6:0];
	assign rd_1 = ((opcode_1 != 7'b0100011) ? inst1[11:7] : 0); // set Rd to 0 if sw instruction
	assign imm_1 = (inst1[6:0] == 7'b0100011) ? {inst1[31:25], inst1[11:7]} : inst1[31:20]; // special check for store word
	// extract control signals from instruction 1
	assign MemRead_1 = ({funct3_1, opcode_1} == 10'b0100000011); // only on LW instruction
	assign MemtoReg_1 = MemRead_1; // only  on LW instruction
	assign MemWrite_1 = ({funct3_1, opcode_1} == 10'b0100100011); // only on SW instruction
	assign RegWrite_1 = (opcode_1 != 7'b0100011); // rd used for everything except SW instruction
	assign ALUSrc_1 = (opcode_1 != 7'b0110011); // everything EXCEPT R-type uses immediate (1 means use immediate)
	always @(funct3_1) begin
		case (funct3_1)
			3'b000: ALUOp_1 <= (inst1[31:29] == 3'b000) ? 2'b00 : 2'b01; // ADD if 2nd highest bit is zero, SUB if 2nd highest bit is one
			3'b110: ALUOp_1 <= 2'b10; // OR
			3'b111: ALUOp_1 <= 2'b11; // AND
			default: ALUOp_1 <= 2'b00; // defaults to ADD
		endcase
	end

	// extract bit sequences from instruction 2
	assign funct7_2 = inst2[31:25];
	assign rs2_2 = inst2[24:20];
	assign rs1_2 = inst2[19:15];
	assign funct3_2 = inst2[14:12];
	assign opcode_2 = inst2[6:0];
	assign rd_2 = ((opcode_2 != 7'b0100011) ? inst2[11:7] : 0); // set Rd to 0 if sw instruction
	assign imm_2 = (inst2[6:0] == 7'b0100011) ? {inst2[31:25], inst2[11:7]} : inst2[31:20]; // special check for store word
	// extract control signals from instruction 2
	assign MemRead_2 = ({funct3_2, opcode_2} == 10'b0100000011); // only on LW instruction
	assign MemtoReg_2 = MemRead_2; // only  on LW instruction
	assign MemWrite_2 = ({funct3_2, opcode_2} == 10'b0100100011); // only on SW instruction
	assign RegWrite_2 = (opcode_2 != 7'b0100011); // rd used for everything except SW instruction
	assign ALUSrc_2 = (opcode_2 != 7'b0110011); // everything EXCEPT R-type uses immediate (1 means use immediate)
	always @(funct3_2) begin
		case (funct3_2)
			3'b000: ALUOp_2 <= (inst2[31:29] == 3'b000) ? 2'b00 : 2'b01; // ADD if 2nd highest bit is zero, SUB if 2nd highest bit is one
			3'b110: ALUOp_2 <= 2'b10; // OR
			3'b111: ALUOp_2 <= 2'b11; // AND
			default: ALUOp_2 <= 2'b00; // defaults to ADD
		endcase
	end

endmodule
