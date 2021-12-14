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
		$display("valid=%d destreg=%d olddestreg=%d PC=%h complete=%d, rdval=%d, storeaddr=%d, storedata=%d, sw=%b", valid, destreg, olddestreg, PC, complete, rdval, storeaddr, storedata, sw);
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
	reg in_use, used, rs1ready, rs2ready;
	reg [1:0] FU; // which functional unit to use for complete? /* 0: invalid, 1: ALU1, 2: ALU2, 3: MEM */ use this to pick between memOP and aluOP
	reg memOP; // which memory operation should the MEM FU perform? /* 0: lw, 1: sw */
	reg [1:0] aluOP; // which operation should the ALU FU perform? /* 0: add, 1: sub, 2: OR, 3: AND */
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
		this.used = 1;
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
		this.used = 0;
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
	reg [3:0] issres; // RS entry to issue to FU
	
	reg memOP_3; // 0: lw, 1: sw denoted for MEM FU
	reg [31:0] memrs1val_3, memrs2val_3, memimm_3, memrdval_3, swaddr_3, swdata_3, raddr_3, rdata_3; // data to read/write to memory in COMPLETE
	reg [31:0] waddr_Ret, wdata_Ret; // data and address to write to memory in RETIRE
	reg MemWrite_Ret; // control signals to MEM FU in COMPLETE
	reg MemRetired; // tracks if 1 store word has already been RETIRED

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
	reg [3:0] alu1ROBnum = 15, alu2ROBnum = 15, memROBnum = 15; // track which ROB entry to complete to
	reg aluSrc_1, aluSrc_2, aluv_1 = 0, aluv_2 = 0, memv_3 = 0; 

	datamem datamemory(.raddr(raddr_3), .waddr(waddr_Ret), .readdata(rdata_3), .writedata(wdata_Ret));
	// Functional Units
	MEM mem3(.memOP(memOP_3), .rs1val(memrs1val_3), .rs2val(memrs2val_3), .imm(memimm_3), .rdval(memrdval_3), .swaddr(swaddr_3), .swdata(swdata_3), .raddr(raddr_3), .rdata(rdata_3)); // MEM FU
	ALU alu1(.aluOP(aluOP_1), .aluSrc(aluSrc_1), .rs1val(alurs1val_1), .rs2val(alurs2val_1), .imm(aluimm_1), .rdval(alurdval_1)); // ALU1
	ALU alu2(.aluOP(aluOP_2), .aluSrc(aluSrc_2), .rs1val(alurs1val_2), .rs2val(alurs2val_2), .imm(aluimm_2), .rdval(alurdval_2)); // ALU2

	reg [31:0] PC;
	initial PC = 0; // keep track of which ROB entry to retire
	reg [1:0] FU; // keep track of functional unit to dispatch 
	bit FUpicker = 0; // track which ALU to issue to

	int nextret[$];
	int freeROB[$];
	int freeRS[$];
	int fwdRS[$];
	int compROB[$];
	int RSready[$];
	int usedbitsum;
	
	always @(posedge clk) begin
		/* RETIRE STAGE */	//max 2 instructions
		// first retire
		nextret = ROB.find_first_index() with (item.PC == PC);
		if(nextret.size() > 0) begin
			ret = nextret.pop_front();
			if(ROB[ret].complete) begin
				if(ROB[ret].sw) begin		// store word retiring: write swdata to swaddr
					wdata_Ret = ROB[ret].storedata;
//					$display("SW Data 1: %d", wdata_Ret);
					waddr_Ret = ROB[ret].storeaddr;
					MemRetired = 1'b1;
				end else begin			// any other instruction retiring: write to register file destination
					freereg_1 = ROB[ret].olddestreg; // free old preg in free pool
					if(ROB[ret].destreg != 0) begin// only write back to registers other than p0
						regfile[ROB[ret].destreg] = ROB[ret].rdval;	// need to write back to regfile the data given by COMPLETE
						fwdRS = RS.find_index() with (item.in_use & ROB[item.ROBnum].valid & (item.rs1 == ROB[ret].destreg | item.rs2 == ROB[ret].destreg));
						foreach(fwdRS[i]) begin
							if(RS[fwdRS[i]].rs1 == ROB[ret].destreg) begin
								if(RS[fwdRS[i]].rs1 != 0) begin
									RS[fwdRS[i]].rs1val = ROB[ret].rdval; // fwd alu1 to rs1
									RS[fwdRS[i]].rs1ready = 1'b1; // update ready bit
//									$display("FWD from RETIRE 1: rs1=%d", ROB[ret].rdval);
								end
							end else if (RS[fwdRS[i]].rs2 == ROB[ret].destreg) begin
								if(RS[fwdRS[i]].rs2 != 0) begin
									RS[fwdRS[i]].rs2val = ROB[ret].rdval; // fwd alu1 to rs1
									RS[fwdRS[i]].rs2ready = 1'b1; // update ready bit
//									$display("FWD from RETIRE 1: rs2=%d", ROB[ret].rdval);
								end
							end
						end
					end
				end
				$display("RETIRED PC: %h", PC);
				ROB[ret].print();
				ROB[ret].clear(); // delete entry from ROB
				PC = PC + 4; // increment PC to track in order RETIREment
				
			end
		end
		// second retire
		nextret = ROB.find_first_index() with (item.PC == PC);
		if(nextret.size() > 0) begin
			ret = nextret.pop_front();
			if(ROB[ret].complete) begin
				if(ROB[ret].sw & ~MemRetired) begin // store word retiring: write swdata to swaddr if a sw hasn't already been RETIRED
					wdata_Ret = ROB[ret].storedata;
//					$display("SW Data 2: %d", wdata_Ret);
					waddr_Ret = ROB[ret].storeaddr;
				end else if (~ROB[ret].sw) begin	// any non-sw instruction retiring: write to register file destination
					freereg_2 = ROB[ret].olddestreg; // free old preg in free pool
					if(ROB[ret].destreg != 0) begin // only write back to registers other than p0
						regfile[ROB[ret].destreg] = ROB[ret].rdval;	// need to write back to regfile the data given by COMPLETE
						fwdRS = RS.find_index() with (item.in_use & ROB[item.ROBnum].valid & (item.rs1 == ROB[ret].destreg | item.rs2 == ROB[ret].destreg));
						foreach(fwdRS[i]) begin
							if(RS[fwdRS[i]].rs1 == ROB[ret].destreg) begin
								if(RS[fwdRS[i]].rs1 != 0) begin
									RS[fwdRS[i]].rs1val = ROB[ret].rdval; // fwd alu1 to rs1
									RS[fwdRS[i]].rs1ready = 1'b1; // update ready bit
//									$display("FWD from RETIRE 2: rs1=%d", ROB[ret].rdval);
								end
							end else if (RS[fwdRS[i]].rs2 == ROB[ret].destreg) begin
								if(RS[fwdRS[i]].rs2 != 0) begin
									RS[fwdRS[i]].rs2val = ROB[ret].rdval; // fwd alu1 to rs1
									RS[fwdRS[i]].rs2ready = 1'b1; // update ready bit
//									$display("FWD from RETIRE 2: rs2=%d", ROB[ret].rdval);
								end
							end
						end
					end
				end
				$display("RETIRED PC: %h", PC);
				ROB[ret].print();
				ROB[ret].clear(); // delete entry from ROB
				PC = PC + 4; // increment PC to track in order RETIREment
			end
		end 
		MemRetired = 1'b0;

		/* COMPLETE STAGE */	// max 3 instructions (2 ALU + 1 MEM)			
		// forward values to respective source regs in Reservation Station
		fwdRS = RS.find_index() with (item.in_use /*& ROB[item.ROBnum].valid*/ & (item.rs1 == alu1Rd | item.rs2 == alu1Rd | item.rs1 == alu2Rd | item.rs2 == alu2Rd | item.rs1 == memRd | item.rs2 == memRd)); // finds all entries requiring forwarding
		foreach(fwdRS[i]) begin
			if(aluv_1 & RS[fwdRS[i]].rs1 == alu1Rd) begin
				if(RS[fwdRS[i]].rs1 != 0) begin
					RS[fwdRS[i]].rs1val = alurdval_1; // fwd alu1 to rs1
					RS[fwdRS[i]].rs1ready = 1'b1; // update ready bit
				end
			end
			else if (aluv_2 & RS[fwdRS[i]].rs1 == alu2Rd) begin
				if(RS[fwdRS[i]].rs1 != 0) begin
					RS[fwdRS[i]].rs1val = alurdval_2; // fwd alu2 to rs1
					RS[fwdRS[i]].rs1ready = 1'b1; // update ready bit
				end
			end
			if(aluv_1 & RS[fwdRS[i]].rs2 == alu1Rd) begin
				if(RS[fwdRS[i]].rs2 != 0) begin
					RS[fwdRS[i]].rs2val = alurdval_1; // fwd alu1 to rs2
					RS[fwdRS[i]].rs2ready = 1'b1; // update ready bit
				end
			end
			else if (aluv_2 & RS[fwdRS[i]].rs2 == alu2Rd) begin
				if(RS[fwdRS[i]].rs2 != 0) begin
					RS[fwdRS[i]].rs2val = alurdval_2;  // fwd alu2 to rs2
					RS[fwdRS[i]].rs2ready = 1'b1; // update ready bit
				end
			end
			if(memv_3 & RS[fwdRS[i]].rs1 == memRd) begin
				if(!ROB[RS[fwdRS[i]].ROBnum].sw & RS[fwdRS[i]].rs1 != 0) begin // only fwd for LW not SW
//					$display("FWD LW: rs1val=%d", memrdval_3);
					RS[fwdRS[i]].rs1val = memrdval_3; // fwd mem to rs1
					RS[fwdRS[i]].rs1ready = 1'b1; // update ready bit
				end
			end
			else if (memv_3 & RS[fwdRS[i]].rs2 == memRd) begin
				if(!ROB[RS[fwdRS[i]].ROBnum].sw & RS[fwdRS[i]].rs2 != 0) begin // only fwd for LW not SW
//					$display("FWD LW: rs2val=%d", memrdval_3);
					RS[fwdRS[i]].rs2val = memrdval_3;  // fwd mem to rs2
					RS[fwdRS[i]].rs2ready = 1'b1; // update ready bit
				end
			end
		end
		// update Rd vals in ROB using ALU/MEM vals and mark as complete and set destreg to ready
		compROB = ROB.find_index() with (item.valid & ~item.complete & (item.index == alu1ROBnum | item.index == alu2ROBnum | item.index == memROBnum));
		foreach(compROB[i]) begin
			if(compROB[i] == alu1ROBnum & aluv_1) begin
				regready[ROB[compROB[i]].destreg] = 1'b1; // ready destreg
				ROB[compROB[i]].rdval = alurdval_1; // update final rdval in ROB
				ROB[compROB[i]].complete = 1'b1; // mark ROB entry as complete
				aluv_1 = 0;
//				$display("Completed Instruction ALU 1 at ROB index: %d ALU1ROBnum: %d", i, alu1ROBnum);
//				ROB[compROB[i]].print();
			end
			else if (compROB[i] == alu2ROBnum & aluv_2) begin
				regready[ROB[compROB[i]].destreg] = 1'b1; // ready destreg
				ROB[compROB[i]].rdval = alurdval_2; // update final rdval in ROB
				ROB[compROB[i]].complete = 1'b1; // mark ROB entry as complete
				aluv_2 = 0;
//				$display("Completed Instruction ALU 2 at ROB index: %d", i);
//				ROB[compROB[i]].print();
			end
			else if (compROB[i] == memROBnum & memv_3) begin
				regready[ROB[compROB[i]].destreg] = 1'b1; // ready destreg
				if(~ROB[compROB[i]].sw) begin // complete lw
					ROB[compROB[i]].rdval = rdata_3; // update final rdval in ROB for lw instructions
//					$display("Complete LW: rdval=%d", rdata_3);
				end
				else if(ROB[compROB[i]].sw) begin // complete sw
					ROB[compROB[i]].storeaddr = swaddr_3;
					ROB[compROB[i]].storedata = swdata_3;
				end
				ROB[compROB[i]].complete = 1'b1; // mark ROB entry as complete
				memv_3 = 0;
//				$display("Completed Instruction MEM 3 at ROB index: %d", i);
//				ROB[compROB[i]].print();
			end
		end

		/* ISSUE STAGE */	// max 3 instructions (2 ALU + 1 MEM)
		
		// if FU's are ready, issue instructions to the FU; also update alu1Rd, alu2Rd, and memRd pipeline register for COMPLETE's forwarding
		RSready = RS.find_first_index() with (item.in_use & item.rs1ready & item.rs2ready & item.FU == 1); // find all RS entries ready to be issued to FU 1 (ALU) based on RS in use and rs1/rs2 ready
		// instruction 1
		if(RSready.size() > 0) begin
			issres = RSready.pop_front(); // pop first RS entry index ready to be issued
			aluOP_1 = RS[issres].aluOP;
			alurs1val_1 = RS[issres].rs1val;
			alurs2val_1 = RS[issres].rs2val;
			aluSrc_1 = RS[issres].ALUSrc;
			alu1Rd = RS[issres].rd;
			alu1ROBnum = RS[issres].ROBnum;
			aluimm_1 = RS[issres].imm;
			aluv_1 = 1;
//			$display("Issued ALU FU 1, PC=%h", ROB[RS[issres].ROBnum].PC);
			RS[issres].print();
			RS[issres].clear(); // clear row in Reservation Station after issuing
		end
		// instruction 2
		RSready = RS.find_first_index() with (item.in_use & item.rs1ready & item.rs2ready & item.FU == 2); // find all RS entries ready to be issued to FU 2 (MEM) based on RS in use and rs1/rs2 ready
		if(RSready.size() > 0) begin
			issres = RSready.pop_front(); // pop first RS entry index ready to be issued
			aluOP_2 = RS[issres].aluOP;
			alurs1val_2 = RS[issres].rs1val;
			alurs2val_2 = RS[issres].rs2val;
			aluSrc_2 = RS[issres].ALUSrc;
			alu2Rd = RS[issres].rd;
			alu2ROBnum = RS[issres].ROBnum;
			aluimm_2 = RS[issres].imm;
			aluv_2 = 1;
//			$display("Issued ALU FU 2");
//			RS[issres].print();
			RS[issres].clear(); // clear row in Reservation Station after issuing
		end 
		// instruction 3
		RSready = RS.find_first_index() with (item.in_use & item.rs1ready & item.rs2ready & item.FU == 3); // find all RS entries ready to be issued to FU 3 (MEM) based on RS in use and rs1/rs2 ready
		if(RSready.size() > 0) begin
			issres = RSready.pop_front(); // pop first RS entry index ready to be issued
			memOP_3 = RS[issres].memOP;
			memrs1val_3 = RS[issres].rs1val;
			memrs2val_3 = RS[issres].rs2val;
			memimm_3 = RS[issres].imm;
			memRd = (ROB[RS[issres].ROBnum].sw) ? 0 : RS[issres].rd; // set destination register to rd for lw and 0 for sw based on sw bit in ROB entry
			memROBnum = RS[issres].ROBnum;
			memv_3 = 1;
//			$display("Issued MEM FU 3");
//			RS[issres].print();
//			ROB[RS[issres].ROBnum].print(); 
			RS[issres].clear(); // clear row in Reservation Station after issuing
		end 

		/* DISPATCH STAGE */
		// update used bits in RS to keep pseudo in order dispatching and make sure entries don't keep filling row 0 and 1
		usedbitsum = 0;
		foreach(RS[i]) if(RS[i].used) usedbitsum++;
		if (usedbitsum >= 13) foreach(RS[i]) RS[i].used = 0;
		// instruction 1
		freeRS = RS.find_first_index() with (item.in_use == 0 & item.used == 0);
		freeROB = ROB.find_first_index() with (item.valid == 0);
		if(freeRS.size() > 0 & freeROB.size() > 0 & (MemWrite_1 | RegWrite_1)) begin
			dispres = freeRS.pop_front(); // find first free entry in reservation station
			disprob = freeROB.pop_front(); // find first free entry in ROB
			FU = (MemRead_1 | MemWrite_1) ? 2'd3 : (FUpicker ? 2'd2 : 2'd1); // picks ALU vs. MEM based on MEM (ALU1 for inst1, ALU2 for inst2)
			if (FU != 3) FUpicker = ~FUpicker;	
//			$display("PC: %d, rs2: %d, rs2ready: %d", PC_R1, rs2_1, regready[rs2_1]);
			RS[dispres].set(regready[rs1_1], regready[rs2_1], FU, MemWrite_1, ALUOp_1, disprob, rd_1, rs1_1, rs2_1, regfile[rs1_1], regfile[rs2_1], imm_1, ALUSrc_1); // add entry to RS
			ROB[disprob].dispatch(rd_1, olddest_1, PC_R1, MemWrite_1); // add entry to ROB
			if(rd_1 != 0) regready[rd_1] = 1'b0; // set rd as unready if it's not p0
//			$display("Dispatched Inst1 to ROB and RS");
//			RS[dispres].print();
//			ROB[disprob].print();
		end
		// instruction 2
		freeRS = RS.find_first_index() with (item.in_use == 0 & item.used == 0);
		freeROB = ROB.find_first_index() with (item.valid == 0);
		if(freeRS.size() > 0 & freeROB.size() > 0 & (MemWrite_2 | RegWrite_2)) begin
			dispres = freeRS.pop_front(); // find first free entry in reservation station 
			disprob = freeROB.pop_front(); // find first free entry in ROB
			FU = (MemRead_2 | MemWrite_2) ? 2'd3 : (FUpicker ? 2'd2 : 2'd1); // picks ALU vs. MEM based on MEM (ALU1 for inst1, ALU2 for inst2)
			if (FU != 3) FUpicker = ~FUpicker;	
//			$display("PC: %d, rs2: %d, rs2ready: %d", PC_R2, rs2_2, regready[rs2_2]);
			RS[dispres].set(regready[rs1_2], regready[rs2_2], FU, MemWrite_2, ALUOp_2, disprob, rd_2, rs1_2, rs2_2, regfile[rs1_2], regfile[rs2_2], imm_2, ALUSrc_2); // add entry to RS
			ROB[disprob].dispatch(rd_2, olddest_2, PC_R2, MemWrite_2); // add entry to ROB
			if(rd_2 != 0) regready[rd_2] = 1'b0; // set rd as unready if it's not p0
//			$display("Dispatched Inst2 to ROB and RS");
//			RS[dispres].print();
//			ROB[disprob].print();
		end
		
	end
endmodule
