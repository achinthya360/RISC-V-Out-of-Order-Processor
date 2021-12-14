`timescale 1ns/1ns 
module fetch(clk, pc, inst1, inst2, done);
	// parameter to set length of instMem text file
	parameter INST_MEM_LENGTH = 1024;

	input clk;
	reg [7:0] instMem[0:INST_MEM_LENGTH-1];
	input [31:0] pc;
	output reg [31:0] inst1, inst2;	

	reg [4:0] donecounter; // when 5 instructions of all zeroes are counted, we end the processing
	output reg done;

	integer instmemfile;
	
	// initial block sets up instruction memory from text file
	integer i = 0;
	initial begin
		done = 1'b0;
		instmemfile = $fopen("instMem-t.txt", "r");  
		while(!$feof(instmemfile)) begin
			// read in instMem in decimal
			$fscanf(instmemfile, "%d\n", instMem[i]); 
			i = i+1;
		end
		/* displays memory loaded in from text file
		for(i = 0; i<INST_MEM_LENGTH; i = i+1) begin
			$display("instMem[%0d] = 0x%0d", i, instMem[i]);
		end
		*/
		$fclose(instmemfile);
		#10;
	end

	// instruction FETCH
	always @(posedge clk) begin
		casez(instMem[pc]) 
			8'bxxxxxxxx: inst1 <= 32'd0;
			default: inst1 <= {instMem[pc+3], instMem[pc+2], instMem[pc+1], instMem[pc]};
		endcase
		casez(instMem[pc+4]) 
			8'bxxxxxxxx: inst2 <= 32'd0;
			default: inst2 <= {instMem[pc+7], instMem[pc+6], instMem[pc+5], instMem[pc+4]};
		endcase
		//pc <= pc + 8;

		if (inst1 == 32'd0) begin
			if(donecounter == 32'd10) begin
				done = 1'b1;
			end
			donecounter = donecounter+1;
		end
		else begin
			donecounter = 32'd0;
		end
	end

endmodule
