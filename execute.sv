class ROBentry;
	reg valid, complete;
	reg [6:0] destreg, olddestreg;
	reg [31:0] PC;
	reg [31:0] rdval;
	reg [31:0] storeaddr, storedata;
	reg sw; // signifies if operation is sw
	function void clear();
		this.valid = 0;
		this.complete = 0;
		this.destreg = 0;
		this.olddestreg = 0;
		this.PC = 0;
		this.rdval = 0;
		this.storeaddr = 0;
		this.storedata = 0;
		this.sw = 0;
	endfunction
	
	function void print();
		$display("valid=%d destreg=%d olddestreg=%d PC=%d complete=%d, rdval=%d", valid, destreg, olddestreg, PC, complete, rdval);
	endfunction
	
	function new ();
		this.valid = 0;
		this.complete = 0;
		this.destreg = 0;
		this.olddestreg = 0;
		this.PC = 0;
		this.rdval = 0;
		this.storeaddr = 0;
		this.storedata = 0;
		this.sw = 0;
	endfunction
	function void dispatch (bit[6:0] destreg, bit[6:0] olddestreg, bit[31:0] PC, bit sw);
		this.valid = 1;
		this.complete = 0;
		this.destreg = destreg;
		this.olddestreg = olddestreg;
		this.PC = PC;
		this.rdval = 0;
		this.storeaddr = 0;
		this.storedata = 0;
		this.sw = sw;
	endfunction
endclass

class RSentry;
	reg in_use, rs1ready, rs2ready;
	reg [1:0] FU; // which functional unit to use for complete? /* 0: invalid, 1: ALU1, 2: ALU2, 3: MEM */ use this to pick between memOP and aluOP
	reg memOP; // which memory operation should the MEM FU perform? /* 0: lw, 1: sw */
	reg [2:0] aluOP; // which operation should the ALU FU perform? /* 0: add, 1: sub, 2: OR, 3: AND */
	reg [3:0] ROBnum; // link to ROB for retiring in order
	reg [6:0] rd, rs1, rs2; // which physical registers does this instruction use?
	reg [31:0] rs1val, rs2val; // what's stored in rs1 and rs2
	reg [31:0] imm; // immediate for I-type or mem instructions
	reg ALUSrc; // 0: use rs2; 1: use immediate
	function void set (bit rs1ready, rs2ready,
			bit [1:0] FU,
			bit memOP,
			bit [2:0] aluOP,
			bit [3:0] ROBnum,
			bit [6:0] rd, rs1, rs2, 
			bit [31:0] rs1val, rs2val, imm,
			bit ALUSrc);
		this.in_use = 1;
		this.rs1ready = rs1ready;
		this.rs2ready = rs2ready;
		this.FU = FU;
		this.memOP = memOP;
		this.aluOP = aluOP;
		this.ROBnum = ROBnum;
		this.rd = rd;
		this.rs1 = rs1;
		this.rs2 = rs2;
		this.rs1val = rs1val;
		this.rs2val = rs2val;
		this.imm = imm; 
		this.ALUSrc = ALUSrc;
	endfunction
	function void clear();
		this.in_use = 0;
		this.rs1ready = 0;
		this.rs2ready = 0;
		this.FU = 0;
		this.memOP = 0;
		this.aluOP = 0;
		this.ROBnum = 0;
		this.rd = 0;
		this.rs1 = 0;
		this.rs2 = 0;
		this.rs1val = 0;
		this.rs2val = 0;
		this.imm = 0;
		this.ALUSrc = 0;
	endfunction
	
	function void print();
		$display("in_use=%d memOP=%d aluOP=%d rd=%d rs1=%d rs1ready=%d rs1val=%d rs2=%d rs2ready=%d rs2val=%d FU=%d ROBnum=%d imm=%d ALUSrc=%d", 
			this.in_use, this.memOP, this.aluOP, this.rd, this.rs1, this.rs1ready, this.rs1val, 
			this.rs2, this.rs2ready, this.rs2val, this.FU, this.ROBnum, this.imm, this.ALUSrc);
	endfunction
	
	function new (); // empty constructor
		this.in_use = 0;
		this.rs1ready = 0;
		this.rs2ready = 0;
		this.FU = 0;
		this.memOP = 0;
		this.aluOP = 0;
		this.ROBnum = 0;
		this.rd = 0;
		this.rs1 = 0;
		this.rs2 = 0;
		this.rs1val = 0;
		this.rs2val = 0;
		this.imm = 0;
		this.ALUSrc = 0;
	endfunction
endclass

module execute(clk, rs1_1, rs2_1, rd_1, rs1_2, rs2_2, rd_2, olddest_1, olddest_2, imm_1, imm_2, 
	MemRead_1, MemtoReg_1, MemWrite_1, ALUSrc_1, RegWrite_1,
	MemRead_2, MemtoReg_2, MemWrite_2, ALUSrc_2, RegWrite_2,
	ALUOp_1, ALUOp_2,
	freereg_1, freereg_2,
	PC_R1, PC_R2);

	input clk; // clk input from top level module
	input [6:0] rs1_1, rs2_1, rd_1, rs1_2, rs2_2, rd_2, olddest_1, olddest_2; // physical registers after renaming
	input [31:0] imm_1, imm_2; // immediates
	input MemRead_1, MemtoReg_1, MemWrite_1, ALUSrc_1 /* 0: rs2, 1: imm */, RegWrite_1; 
	input MemRead_2, MemtoReg_2, MemWrite_2, ALUSrc_2 /* 0: rs2, 1: imm */, RegWrite_2;  
	input [1:0] ALUOp_1, ALUOp_2; // 00: ADD, 01: SUB, 10: OR, 11: AND
	input [31:0] PC_R1, PC_R2; // PC from RENAME to store in ROB for retiring in order

	output reg [6:0] freereg_1 = 0, freereg_2 = 0; // pregs to free in free pool

	reg [3:0] ret; // ROB entry to retire (15 possible in ROB)
	reg [3:0] dispres; // RS entry to dispatch into (15 possible in RS)
	reg [3:0] disprob; // ROB entry to dispatch into (15 possible in ROB)
	RSentry issueentry; // RS entry to issue to FU
	
	reg memOP_3; // 0: lw, 1: sw denoted for MEM FU
	reg [6:0] ; // memory address to read from or write back to in COMPLETE
	reg [31:0] memrs1val_3, memrs2val_3, imm_3, memdval_3, swaddr_3, swdata_3, raddr_3, rdata_3; // data to read/write to memory in COMPLETE
	reg MemWrite_C, MemRead_C; // control signals to MEM FU in COMPLETE

	RSentry RS[0:15]; // setup Reservation Station with all zeros initially
	initial foreach (RS[i]) RS[i] = new();

	ROBentry ROB[0:15]; // setup ROB with all zeros initially
	initial	foreach (ROB[i]) ROB[i] = new();
	
	reg [31:0] regfile [0:127]; // register file of all physical registers
	initial foreach(regfile[i]) regfile[i] = 0; // initialize all to 0 
	
	reg FUready [0:2]; // Functional Unit readiness table
	initial foreach (FUready[i]) FUready[i] = 1'b1; // initially set all FUs to ready

	reg regready [0:127]; // register readiness table
	initial foreach (regready[i]) regready[i] = 1'b1; // initially set all registers to ready

	reg [1:0] aluOP_1, aluOP_2; // information storage for ALUs in COMPLETE stage
	reg [31:0] alurs1val_1, alurs2val_1, alurdval_1, alurs1val_2, alurs2val_2, alurdval_2, aluimm_1, aluimm_2;
	reg [6:0] alu1Rd, alu2Rd, memRd;

	MEM(.memOP(memOP_3), .rs1val(memrs1val_3), .rs2val(memrs2val_3), .imm(imm_3), .rdval(memrdval_3), .swaddr(swaddr_3), .swdata(swdata_3), .raddr(raddr_3), .rdata(rdata_3)); // MEM FU
	ALU alu1(.aluOP(aluOP_1), .aluSrc(ALUSrc_1), .rs1val(alurs1val_1), .rs2val(alurs2val_1), .imm(aluimm_1), .rdval(alurdval_1)); // ALU1
	ALU alu2(.aluOP(aluOP_2), .aluSrc(ALUSrc_2), .rs1val(alurs1val_2), .rs2val(alurs2val_2), .imm(aluimm_2), .rdval(alurdval_2)); // ALU2

	reg [31:0] PC;
	initial PC = 0; // keep track of which ROB entry to retire
	reg [1:0] FU; // keep track of functional unit to dispatch 

	int nextret[$];
	int freeROB[$];
	int freeRS[$];
	int fwdRS[$];
	int compROB[$];
	int RSready[$];
	
	always @(posedge clk) begin

//		begincomment for testing each stage
//		/* RETIRE STAGE */	max 2 instructions
//		// first retire
//		nextret = ROB.find_first_index() with (item.PC == PC);
//		if(nextret.size() > 0) begin
//			ret = nextret.pop_front();
//			if(ROB[ret].complete) begin
//				freereg_1 = ROB[ret].olddestreg; // free old preg in free pool
//				regfile[ROB[ret].destreg] = ROB[ret].rdval;	// need to write back to regfile the data given by COMPLETE
//				// problem: need to keep track of which functional unit has the right data to write back
//				ROB[ret].clear(); // delete entry from ROB
//				PC = PC + 4; // increment PC to track in order RETIREment
//			end
//		end
//		// second retire
//		nextret = ROB.find_first_index() with (item.PC == PC);
//		if(nextret.size() > 0) begin
//			ret = nextret.pop_front();
//			if(ROB[ret].complete) begin
//				freereg_2 = ROB[ret].olddestreg; // free old preg in free pool
//				regfile[ROB[ret].destreg] = ROB[ret].rdval;	// need to write back to regfile the data given by COMPLETE
//				// problem: need to keep track of which functional unit has the right data to write back
//				ROB[ret].clear(); // delete entry from ROB
//				PC = PC + 4; // increment PC to track in order RETIREment
//			end
//		end
//
//		/* COMPLETE STAGE */	max 3 instructions (2 ALU + 1 MEM)
//		// forward values to respective source regs in Reservation Station
//		fwdRS = RS.find_index() with (item.rs1 == alu1Rd | item.rs2 == alu1Rd | item.rs1 == alu2Rd | item.rs2 == alu2Rd | item.rs1 == memRd | item.rs2 == memRd); // finds all entries requiring forwarding
//		foreach(fwdRS[i]) begin
//			if(RS[fwdRS[i]].rs1 == alu1Rd) RS[fwdRS[i]].rs1val = alurdval_1; // fwd alu1 to rs1
//			else if (RSfwdRS[i].rs1 == alu2Rd) RS[fwdRS[i]].rs1val = alurdval_2; // fwd alu2 to rs1
//			if(RS[fwdRS[i]].rs2 == alu1Rd) RS[fwdRS[i]].rs2val = alurdval_1; // fwd alu1 to rs2
//			else if (RSfwdRS[i].rs2 == alu2Rd) RS[fwdRS[i]].rs2val = alurdval_2;  // fwd alu2 to rs2
//			if(RS[fwdRS[i]].rs2 == memRd) RS[fwdRS[i]].rs2val = memRdval; // fwd mem to rs2
//			else if (RSfwdRS[i].rs2 == memRd) RS[fwdRS[i]].rs2val = memRdval;  // fwd mem to rs2
//		end
//		// update Rd vals in ROB using ALU/MEM vals and mark as complete and set destreg to ready
//		compROB = ROB.find_index() with (item.destreg == alu1Rd | item.destreg == alu2Rd | item.destreg == memRd);
//		foreach(compROB[i]) begin
//			if(ROB[compROB[i]].destreg == alu1Rd) begin
//				regready[ROB[compROB[i]].destreg] = 1'b1; // ready destreg
//				ROB[compROB[i]].rdval = alurdval_1; // update final rdval in ROB
//				ROB[compROB[i]].complete = 1'b1; // mark ROB entry as complete
//			end
//			else if (ROB[compROB[i]].destreg == alu2Rd) begin
//				regready[ROB[compROB[i]].destreg] = 1'b1; // ready destreg
//				ROB[compROB[i]].rdval = alurdval_2; // update final rdval in ROB
//				ROB[compROB[i]].complete = 1'b1; // mark ROB entry as complete
//			end
//			else if (ROB[compROB[i]].destreg == memRd) begin
//				regready[ROB[compROB[i]].destreg] = 1'b1; // ready destreg
//				ROB[compROB[i]].rdval = readdata_C; // update final rdval in ROB
//				ROB[compROB[i]].complete = 1'b1; // mark ROB entry as complete
//			end
//		end	
//		endcomment for testing

		/* ISSUE STAGE */	// max 3 instructions (2 ALU + 1 MEM)
		
		// if FU's are ready, issue instructions to the FU; also update alu1Rd, alu2Rd, and memRd pipeline register for COMPLETE's forwarding
		RSready = RS.find_first_index() with (item.in_use & item.rs1ready & item.rs2ready & item.FU == 1); // find all RS entries ready to be issued to FU 1 (ALU) based on RS in use and rs1/rs2 ready
		// instruction 1
		if(RSready.size() > 0) begin
			issueentry = RS[RSready.pop_front()]; // pop first RS entry ready to be issued
			aluOP_1 = issueentry.aluOP;
			alurs1val_1 = issueentry.rs1val;
			alurs2val_1 = issueentry.rs2val;
			ALUSrc_1 = issueentry.ALUSrc;
			alu1Rd = issueentry.rd;
		end
		// instruction 2
		RSready = RS.find_first_index() with (item.in_use & item.rs1ready & item.rs2ready & item.FU == 2); // find all RS entries ready to be issued to FU 2 (MEM) based on RS in use and rs1/rs2 ready
		if(RSready.size() > 0) begin
			issueentry = RS[RSready.pop_front()]; // pop first RS entry ready to be issued
			aluOP_2 = issueentry.aluOP;
			alurs1val_2 = issueentry.rs1val;
			alurs2val_2 = issueentry.rs2val;
			ALUSrc_2 = issueentry.ALUSrc;
			alu2Rd = issueentry.rd;
		end
		// instruction 3
		RSready = RS.find_first_index() with (item.in_use & item.rs1ready & item.rs2ready & item.FU == 3); // find all RS entries ready to be issued to FU 3 (MEM) based on RS in use and rs1/rs2 ready
		if(RSready.size() > 0) begin

		end
		

		/* DISPATCH STAGE */
		// instruction 1
		freeRS = RS.find_first_index() with (item.in_use == 0);
		freeROB = ROB.find_first_index() with (item.valid == 0);
		if(freeRS.size() > 0 & freeROB.size() > 0 & (MemWrite_1 | RegWrite_1)) begin
			dispres = freeRS.pop_front(); // find first free entry in reservation station
			disprob = freeROB.pop_front(); // find first free entry in ROB
			FU = (MemRead_1 | MemWrite_1) ? 2'd3 : 2'd1; // picks ALU vs. MEM based on MEM (ALU1 for inst1, ALU2 for inst2)
								
			RS[dispres].set(regready[rs1_1], regready[rs2_1], FU, MemWrite_1, ALUOp_1, disprob, rd_1, rs1_1, rs2_1, regfile[rs1_1], regfile[rs2_1], imm_1, ALUSrc_1); // add entry to RS
			ROB[disprob].dispatch(rd_1, olddest_1, PC_R1, MemWrite_1); // add entry to ROB
			regready[rd_1] = 1'b0; // set rd as unready
			RS[dispres].print();
			ROB[disprob].print();
		end
		// instruction 2
		freeRS = RS.find_first_index() with (item.in_use == 0);
		freeROB = ROB.find_first_index() with (item.valid == 0);
		if(freeRS.size() > 0 & freeROB.size() > 0 & (MemWrite_2 | RegWrite_2)) begin
			dispres = freeRS.pop_front(); // find first free entry in reservation station 
			disprob = freeROB.pop_front(); // find first free entry in ROB
			FU = (MemRead_2 | MemWrite_2) ? 2'd3 : 2'd2; // picks ALU vs. MEM based on MEM (ALU1 for inst1, ALU2 for inst2)
					
			RS[dispres].set(regready[rs1_2], regready[rs2_2], FU, MemWrite_2, ALUOp_2, disprob, rd_2, rs1_2, rs2_2, regfile[rs1_2], regfile[rs2_2], imm_2, ALUSrc_2); // add entry to RS
			ROB[disprob].dispatch(rd_2, olddest_2, PC_R2, MemWrite_2); // add entry to ROB
			regready[rd_2] = 1'b0; // set rd as unready
			RS[dispres].print();
			ROB[disprob].print();
		end
		
	end
endmodule
