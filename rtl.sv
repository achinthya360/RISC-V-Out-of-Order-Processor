module regfile(rs1_1, rs2_1, rd_1, RegWrite_1, rs1data_1, rs2data_1, rddata_1,
		rs1_2, rs2_2, rd_2, RegWrite_2, rs1data_2, rs2data_2, rddata_2);
	
	input [4:0] rs1_1, rs2_1, rd_1, rs1_2, rs2_2, rd_2; // registers used by both instructions
	input [31:0] rddata_1, rddata_2; // data to write to rd
	input RegWrite_1, RegWrite_2; // control signal determining whether to write to Rd
	
	output [31:0] rs1data_1, rs2data_1, rs1data_2, rs2data_2; // output data from source registers for both instructions
	
	reg [31:0] aregs [0:127]; // register file of all physical registers

	// read data1 and data2 for both instructions
	assign rs1data_1 = aregs[rs1_1];
	assign rs2data_1 = aregs[rs2_1];
	assign rs1data_2 = aregs[rs1_2];
	assign rs2data_2 = aregs[rs2_2];

	initial begin
		aregs[0] <= 32'd0; // p0 should always be hardwired zero
	end

	always @(posedge RegWrite_1) begin
		if(rd_1 != 5'd0) begin // only change register value if it's not p0
			aregs[rd_1] <= rddata_1; // write to rd of instruction 1
		end
	end

	always @(posedge RegWrite_2) begin
		if(rd_2 != 5'd0) begin // only change register value if it's not p0
			aregs[rd_2] <= rddata_2; // write to rd of instruction 2
		end
	end
endmodule

module datamem(raddr, waddr, readdata, writedata, MemWrite); // FUNCTIONAL UNIT for accessing data memory
	input [31:0] raddr, waddr, writedata;
	output [31:0] readdata; 
	input MemWrite;
	reg [7:0] instMem[0:1023]; // data memory itself

	assign readdata = {instMem[raddr], instMem[raddr+1], instMem[raddr+2], instMem[raddr+3]};
	
	always @(posedge MemWrite) begin
		{instMem[waddr], instMem[waddr+1], instMem[waddr+2], instMem[waddr+3]} <= writedata;
	end
endmodule

module MEM(memOP, rs1val, rs2val, imm, rdval, swaddr, swdata, raddr, rdata);
	input memOP;
	input [31:0] rs1val, rs2val, imm;
	output [31:0] rdval, swaddr, swdata, raddr; // outputs to execute.sv plus raddr to select address in data memory
	input [31:0] rdata; // read in data from data memory

	assign raddr = rs1val + imm; // set address for lw
	assign swaddr = rs1val + imm; // set address for sw
	assign swdata = rs2val; // M[rs1 + imm] = rs2 <-- output correct data to sw
	assign rdval = rdata; // read from memory for lw
endmodule

module ALU(aluOP, aluSrc, rs1val, rs2val, imm, rdval); // FUNCTIONAL UNIT for ALU operations
	input [1:0] aluOP;
	input aluSrc;
	input [31:0] rs1val, rs2val, imm;
	
	output reg [31:0] rdval;

	always @(*) begin
		case(aluOP)
			2'd0: rdval = rs1val + ((aluSrc) ? imm : rs2val);
			2'd1: rdval = rs1val - rs2val; // subi not supported
			2'd2: rdval = rs1val | ((aluSrc) ? imm : rs2val);
			2'd3: rdval = rs1val & ((aluSrc) ? imm : rs2val);
		endcase
	end
endmodule

/* comment out ROB and RS from this file, moved to execute.sv
class ROBentry;
	reg valid, complete;
	reg [6:0] destreg, olddestreg;
	reg [31:0] PC;
		function void clear();
		this.valid = 0;
		this.complete = 0;
		this.destreg = 0;
		this.olddestreg = 0;
		this.PC = 0;
	endfunction
	
	function void print();
		$display("valid=%d destreg=%d olddestreg=%d PC=%d complete=%d", valid, destreg, olddestreg, PC, valid);
	endfunction
	
	function new ();
		this.valid = 0;
		this.complete = 0;
		this.destreg = 0;
		this.olddestreg = 0;
		this.PC = 0;
	endfunction
		function void dispatch (bit[6:0] destreg, bit[6:0] olddestreg, bit[31:0] PC);
		this.valid = 1;
		this.complete = 0;
		this.destreg = destreg;
		this.olddestreg = olddestreg;
		this.PC = PC;
	endfunction
endclass

class RSentry;
	reg in_use, rs1ready, rs2ready;
	reg [1:0] FU; // which functional unit to use for complete?  0: invalid, 1: ALU1, 2: ALU2, 3: MEM  use this to pick between memOP and aluOP
	reg memOP; // which memory operation should the MEM FU perform?  0: lw, 1: sw 
	reg [2:0] aluOP; // which operation should the ALU FU perform? 0: add, 1: sub, 2: OR, 3: AND 
	reg [3:0] ROBnum; // link to ROB for retiring in order
	reg [6:0] rd, rs1, rs2; // which physical registers does this instruction use?
	reg [31:0] rs1val, rs2val; // what's stored in rs1 and rs2
		function void set (bit rs1ready, rs2ready,
	bit [1:0] FU,
	bit memOP, 
	bit [2:0] aluOP,
	bit [3:0] ROBnum,
	bit [6:0] rd, rs1, rs2, 
	bit [31:0] rs1val, rs2val);
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
	endfunction
	
	function void print();
		$display("in_use=%d memOP=%d aluOP=%d rd=%d rs1=%d rs1ready=%d rs1val=%d rs2=%d rs2ready=%d rs2val=%d FU=%d ROBnum=%d", 
			this.in_use, this.memOP, this.aluOP, this.rd, this.rs1, this.rs1ready, this.rs1val, 
			this.rs2, this.rs2ready, this.rs2val, this.FU, this.ROBnum);
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
	endfunction
endclass
*/
/*module RAT(areg, preg, rename, firstfree);
	input rename; // 1 if the areg needs to link to a new preg in RENAME stage
	input [4:0] areg; // 32 total architectural registers
	output [6:0] preg; // 128 total physical registers 
	input reg [6:0] firstfree; // first free entry in free pool

	reg [6:0] regLinks[0:31]; // stores physical register mapping for each architectural register

	// initially map all architecural regs to their corresponding pregs (i.e. x1 = p1)
	initial begin
		int i;
		for (i = 0; i < 32; i = i + 1) begin
			regLinks[i] = i;
		end
	end

	always @(posedge rename) begin
		if(areg != 5'd0) begin // cannot rename a0 or p0
			regLinks[areg] = firstfree; // only assigns areg to a new preg (need to unfree the preg in free pool in RENAME)
		end
	end
	
	assign preg = regLinks[areg]; // always output preg value linked to input areg
endmodule*/

/* deprecated freepool module
module freepool(preg, pregstatus, pregtofree, freepreg, usepreg, firstfree);
	input [6:0] preg; // input preg we want to check free or free after using it
	input [6:0] pregtofree; // input preg to free after retire
	input freepreg; // set to 1 if we want to free that preg
	input usepreg; // set to 1 when the preg is used by rename
	output reg pregstatus; // returns 1 if the preg is free
	output reg [6:0] firstfree; // returns first preg that's free
	
	reg pool[0:127]; // stores free bit for all physical registers
	reg firstfreepool [1:127]; // stores free bit for all physical registers EXCEPT p0 which is always free
	assign firstfreepool = pool[1:127];

	// set all registers in pool to free initially
	initial begin
		int i;
		for (i = 0; i < 128; i = i + 1) begin
			pool[i] = 1'b1;
		end
	end

	// output the status of whichever preg is being requested
	assign pregstatus = pool[preg];

	// logic to free a preg
	always @(posedge freepreg) begin
		if(preg != 7'd0) begin // p0 should always be free
			pool[preg] <= 1'b1;
		end
	end

	// logic to unfree a preg
	always @(*) begin
		if(preg != 7'd0 & usepreg) begin // p0 should always be free, otherwise unfree
			pool[preg] <= 1'b0;
		end
	end

	// firstfree logic
	int qu[$]; // queue to help with finding first free index
	always @(*) begin
		qu = firstfreepool.find_first_index with (item == 1); // find first free preg index in pool
		$display("Size of qu: %d, qu: %p", qu.size(), qu);
		firstfree <= qu.pop_front();
	end
endmodule
*/