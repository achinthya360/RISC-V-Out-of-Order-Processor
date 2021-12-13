`timescale 1ns/1ns
module rename(rs1_1, rs2_1, rd_1, rs1_2, rs2_2, rd_2, 
		rs1out_1, rs2out_1, rdout_1, rs1out_2, rs2out_2, rdout_2, olddest_1, olddest_2,
		RegWrite_1, RegWrite_2, ALUSrc_1, ALUSrc_2,
		freereg_1, freereg_2);

	input [4:0] rs1_1, rs2_1, rd_1, rs1_2, rs2_2, rd_2; // architectural registers from DECODE
	output reg [6:0] rs1out_1, rs2out_1, rdout_1, rs1out_2, rs2out_2, rdout_2, olddest_1, olddest_2; // physical registers after renaming
	input RegWrite_1, RegWrite_2; // control signals determine whether to use Rd or not
	input ALUSrc_1, ALUSrc_2; // control signals determine whether to use Rs2 or not (1 means imm so no rs2)
	input [6:0] freereg_1, freereg_2; // registers to free from RETIRE

	reg [6:0] RAT[0:31]; // stores physical register mapping for each architectural register
	reg freepool[0:127]; // stores free bit for all physical registers
//	wire firstfreepool [1:127]; // stores free bit for all physical registers EXCEPT p0 which is always free
	reg [6:0] firstfree; // first free preg in free pool
	int qu[$]; // queue to help with finding first free index
	
	// initially map all architecural regs to their corresponding pregs (i.e. x1 = p1)
	initial begin
		int i;
		for (i = 0; i < 32; i = i + 1) begin
			RAT[i] = i;
		end
		for (i = 0; i < 128; i = i + 1) begin
			freepool[i] = 1'b1;
		end
	end
	
	// free register 1 from RETIRE
	always @(freereg_1) begin
		freepool[freereg_1] = 1'b1;
	end
	// free register 2 from RETIRE
	always @(freereg_2) begin
		freepool[freereg_2] = 1'b1;
	end

	always @(*) begin // change in input registers indicates next instructions have been passed from DECODE
		// assign corresponding pregs from RAT for first instruction's source aregs
		rs1out_1 = RAT[rs1_1];
		if(~ALUSrc_1) begin
			rs2out_1 = RAT[rs2_1];
		end
		// rename preg for first destination register
		if(RegWrite_1) begin
			olddest_1 = RAT[rd_1];
			if(rd_1 == 0) begin
				rdout_1 = 0;
			end else begin
				if(freepool[olddest_1]) begin	// if the preg is currently free, use it
					rdout_1 = RAT[rd_1];
					freepool[olddest_1] = 1'b0;
				end else begin		// if the preg is being used, use the next free one from the free pool
					qu = freepool.find_index with (item == 1 && item.index > 0); // find first free preg index in pool
					firstfree = qu.pop_front();
					$display("first free for rd_1: %d", firstfree);
					$display("old dest for rd_1: %d", olddest_1);
					freepool[firstfree] = 1'b0;
					rdout_1 = firstfree;
					RAT[rd_1] = firstfree;
				end
			end
		end
		
		// assign corresponding pregs from RAT for first instruction's source aregs
		rs1out_2 = RAT[rs1_2];
		if(~ALUSrc_2) begin
			rs2out_2 = RAT[rs2_2];
		end
		// rename preg for first destination register
		if(RegWrite_2) begin
			olddest_2 = RAT[rd_2];
			if(rd_2 == 0) begin
				rdout_2 = 0;
			end else begin
				if(freepool[olddest_2]) begin	// if the preg is currently free, use it
					rdout_2 = RAT[rd_2];
					freepool[olddest_2] = 1'b0;
				end else begin		// if the preg is being used, use the next free one from the free pool
					qu = freepool.find_index with (item == 1 && item.index > 0); // find first free preg index in pool
					firstfree = qu.pop_front();
					$display("first free for rd_2: %d", firstfree);
					$display("old dest for rd_2: %d", olddest_2);
					freepool[firstfree] = 1'b0;
					rdout_2 = firstfree;
					RAT[rd_2] = firstfree;
				end
			end
		end
	end
endmodule
