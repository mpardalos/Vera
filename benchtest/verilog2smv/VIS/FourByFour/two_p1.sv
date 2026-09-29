/*
*
*	Taken from VIS Benchmarks <ftp://vlsi.colorado.edu/pub/vis/vis-verilog-models-1.3.tar.gz>
*	Modified by Ahmed Irfan <irfan@fbk.eu>
*
*/
// Slider puzzle reduced to 2 rows and four columns. +----+----+----+----+
//                                                   |  0 |  1 |  2 |  3 |
// The entries of the matrix are numbered thus:      +----+----+----+----+
//                                                   |  4 |  5 |  6 |  7 |
// Author: Fabio Somenzi <Fabio@Colorado.EDU>        +----+----+----+----+

module twoByFour(clock,from,to);
    input       clock;
    input [2:0] from;
    input [2:0] to;

    // CHANGED FOR VERA
    // Was [1:0], which was truncating. Changed to [2:0], which is the
    // correct behaviour
    reg [2:0] 	b[0:7];
    reg [2:0] 	freg, treg;
    wire 	valid, parity;

    // CHANGED FOR VERA
    // Made all literal sizes explicit, to avoid implicit signedness

    initial begin
         b[0]  = 3'd7; b[1]  = 3'd6; b[2]  = 3'd5; b[3]  = 3'd4;
	 b[4]  = 3'd3; b[5]  = 3'd2; b[6]  = 3'd1; b[7]  = 3'd0;
	treg = 3'd0;
	freg = 3'd0;
    end 

    assign valid = (b[treg] == 3'b000) &&
		   (((treg[1:0] == freg[1:0]) && !(treg[2] == freg[2])) ||
		    ((treg[2] == freg[2]) &&
		     (((treg[1:0]==2'b00) && (freg[1:0]==2'b01)) ||
		      ((treg[1:0]==2'b01) && (freg[0]==0)) ||
		      ((treg[1:0]==2'b10) && (freg[0]==1)) ||
		      ((treg[1:0]==2'b11) && (freg[1:0]==2'b10))
		      )
		     )
		    );

    assign parity = 
	   (((b[0] & 3'd5) == 3'd1) | ((b[0] & 3'd5) == 3'd4)) ^
	   (((b[1] & 3'd5) == 3'd0) | ((b[1] & 3'd5) == 3'd5)) ^
	   (((b[2] & 3'd5) == 3'd1) | ((b[2] & 3'd5) == 3'd4)) ^
	   (((b[3] & 3'd5) == 3'd0) | ((b[3] & 3'd5) == 3'd5)) ^
	   (((b[4] & 3'd5) == 3'd1) | ((b[4] & 3'd5) == 3'd4)) ^
	   (((b[5] & 3'd5) == 3'd0) | ((b[5] & 3'd5) == 3'd5)) ^
	   (((b[6] & 3'd5) == 3'd1) | ((b[6] & 3'd5) == 3'd4)) ^
	   (((b[7] & 3'd5) == 3'd0) | ((b[7] & 3'd5) == 3'd5));

    always @ (posedge clock) begin
	freg <= from;
	treg <= to;
    end

    always @ (posedge clock) begin
	if (valid) begin
	    b[treg] <= b[freg];
	    b[freg] <= 3'd0;
	end
    end

/*invariant property
!(b<*0*>[2:0]=0 * b<*1*>[2:0]=1 * b<*2*>[2:0]=2 * b<*3*>[2:0]=3 *
  b<*4*>[2:0]=4 * b<*5*>[2:0]=5 * b<*6*>[2:0]=6 * b<*7*>[2:0]=7);*/
	assert property (	!(b[0]==3'd0 && b[1]==3'd1 && b[2]==3'd2 && b[3]==3'd3 &&
				b[4]==3'd4 && b[5]==3'd5 && b[6]==3'd6 && b[7]==3'd7)		);

//G(parity=0);

endmodule // twoByFour
