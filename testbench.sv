`timescale 1ns/1ns
module testbench(preg_R);
	reg clk;

	// testing free pool
	output reg [6:0] preg_R; // preg communicated between RAT, free pool, and RENAME
	reg [4:0] areg_R; // areg communicated between RAT and RENAME
	reg pregstatus_R; // free status of preg in RENAME
	reg usepreg_R; // unfree preg signal in RENAME, communicated between RAT and free pool
	reg rename_R; // rename signal between RAT and RENAME, RAT automatically communicates this to free pool through usepreg_R
	reg [6:0] firstfree_R; // firstfree preg in renaming process in RENAME stage
	reg [6:0] pregtofree_RE; // preg being freed by RETIRE stage
	reg freepreg_RE; // freeing signal in RETIRE stage

	freepool fp(.preg(preg_R), .pregstatus(pregstatus_R), .pregtofree(pregtofree_RE), .freepreg(freepreg_RE), .usepreg(usepreg_R), .firstfree(firstfree_R));
	RAT rat(.areg(areg_R), .preg(preg_R), .rename(rename_R), .firstfree(firstfree_R));

	initial begin
		clk = 0;
		areg_R = 0;
	end

	always begin
		#4
		clk = ~clk;
	end

	always @(posedge clk) begin
		areg_R = areg_R + 1;
		if(preg_R == 20) begin
			$stop();
		end
		else begin
			usepreg_R = 1'b1;
			#1
			usepreg_R = 1'b0;
			#1
			freepreg_RE = 1'b0;
			#1
			freepreg_RE = 1'b0;
		end
	end

endmodule
