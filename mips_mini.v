
`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date:    21:29:02 11/18/2018 
// Design Name: 
// Module Name:    mip_16_mini 
// Project Name: 
// Target Devices: 
// Tool versions: 
// Description: 
//
// Dependencies: 
//
// Revision: 
// Revision 0.01 - File Created
// Additional Comments: 
//
//////////////////////////////////////////////////////////////////////////////////

//--------------------------------------------------------------
//------------------------------------------------
// mipsmemsingle.v
// External memories used by MIPS single-cycle
//------------------------------------------------

module dmem(input         clk, we,
            input  [15:0] a, wd,
            output [15:0] rd);

  reg  [15:0] RAM[63:0];

  assign rd = RAM[a[15:1]]; // word aligned

  always @(posedge clk) 
	begin
    if (we)		 
   	RAM[a[15:1]] <= wd;
    end
    
endmodule

module imem(input  [5 :0] a,
            output [15:0] rd);

  reg  [15:0] RAM[10:0];
	integer i;
  initial
    begin
	 	 RAM[0] = {3'd7, 3'd0, 3'd3, 7'd9};
		 RAM[2] = {3'd7, 3'd0, 3'd2, 7'd7};
		 RAM[4] = {3'd0, 3'd2, 3'd3, 3'd4, 4'd0};
		 RAM[6] = {3'd2, 13'd0};
//		 RAM[2] = {3'd7, 3'd3, 3'd7, -7'd9};
//		 RAM[3] = {3'd0, 3'd7, 3'd2, 3'd4, 4'd3};
//		 RAM[4] = {3'd0, 3'd3, 3'd4, 3'd5, 4'd2};
//		 RAM[5] = {3'd0, 3'd5, 3'd4, 3'd5, 4'd0};
//		 RAM[6] = {3'd6, 3'd5, 3'd7, 7'd10};
//		 RAM[7] = {3'd0, 3'd3, 3'd4, 3'd4, 4'd4};
//		 RAM[8] = {3'd6, 3'd4, 3'd0, 7'd1};
//		 RAM[9] = {3'd0, 3'd7, 3'd2, 3'd4, 4'd4};
//		 RAM[10] = {3'd7, 3'd0, 3'd5, 7'd0};
//		 RAM[11] = {3'd0, 3'd4, 3'd5, 3'd7, 4'd0};
//		 RAM[12] = {3'd5, 3'd3, 3'd7, 7'd30};
//		 RAM[13] = {3'd0, 3'd7, 3'd2, 3'd7, 4'd1};
//		 RAM[14] = {3'd4, 3'd0, 3'd2, 7'd42};
//		 RAM[15] = {3'd2, 13'd17};
//		 RAM[16] = {3'd7, 3'd0, 3'd2, 7'd1};
//		 RAM[17] = {3'd5, 3'd0, 3'd2, 7'd44};
//		 for (i = 3; i<63; i=i+1) RAM[i] = 0;
    end

  assign rd = RAM[a]; // word aligned
// $display("rd: %h", RAM[a]);
endmodule

//-----------------------------------------------------------------------------------------------------------------------------------------------------------------------
//------------------------------------------------
// mipsparts.v
// Components used in MIPS processor
//------------------------------------------------

module alu(input      [15:0] a, b, 
           input      [2:0]  alucont, 
           output reg [15:0] result,
           output            zero);

  always@(*)
    case(alucont)
      3'b000: result <= a + b;
      3'b001: result <= a - b;
      3'b010: result <= a & b;
      3'b011: result <= a | b;
      3'b100: begin if(a < b) result <= 16'd1;
		    else result <= 16'd0;
		end
      default: result <= a + b;
    endcase

  assign zero = (result == 16'd0) ? 1'b1: 1'b0;
endmodule

module regfile(input         clk, 
               input         we3, 
               input  [2:0]  ra1, ra2, wa3, 
               input  [15:0] wd3, 
               output [15:0] rd1, rd2);

  reg [15:0] rf[15:0];

  // three ported register file
  // read two ports combinationally
  // write third port on rising edge of clock
  // register 0 hardwired to 0

  always @(posedge clk)
    if (we3) rf[wa3] <= wd3;	

  assign rd1 = (ra1 != 0) ? rf[ra1] : 0;
  assign rd2 = (ra2 != 0) ? rf[ra2] : 0;

endmodule

module adder(input [15:0] a, b,
             output [15:0] y);

  assign y = a + b;
endmodule

module sl2(input  [15:0] a,
           output [15:0] y);

  // shift left by 1
  assign y = {a[14:0], 1'b0};
endmodule

module signext(input  [6:0] a,
               output [15:0] y);
              
  assign y = {{9{a[6]}}, a};
endmodule

module flopr #(parameter WIDTH = 8)
              (input                  clk, reset,
               input      [WIDTH-1:0] d, 
               output reg [WIDTH-1:0] q);

  always @(posedge clk, posedge reset)
    if (reset) q <= 0;
    else       q <= d;
endmodule

module flopenr #(parameter WIDTH = 8)
                (input                  clk, reset,
                 input                  en,
                 input      [WIDTH-1:0] d, 
                 output reg [WIDTH-1:0] q);
 
  always @(posedge clk, posedge reset)
    if      (reset) q <= 0;
    else if (en)    q <= d;
endmodule

module mux2 #(parameter WIDTH = 8)
             (input  [WIDTH-1:0] d0, d1, 
              input              s, 
              output [WIDTH-1:0] y);

  assign y = s ? d1 : d0; 
endmodule

module mux4 #(parameter WIDTH = 8)
             (input  [WIDTH-1:0] d0, d1, 
              input  [1:0]       s, 
              output reg [WIDTH-1:0] y);
	always @(d0 or d1 or s)
	begin 
	case(s)
		2'b00 : y <= d0;
		2'b01 : y<= d1;
		default : y<= WIDTH-1'dx;
	endcase
	end
 
endmodule
//-----------------------------------------------------------------------------------------------------------------------------------------------------------------------
//-----------------------------------------------------------------------------------------------------------------------------------------------------------------------
//-----------------------------------------------------------------------------------------------------------------------------------------------------------------------


// single-cycle MIPS processor
module mips(input         clk, reset,
            output [15:0] pc,
            input  [15:0] instr,
            output        memwrite,
            output [15:0] aluout, writedata,
            input  [15:0] readdata,
				output [7:0]  r);

  wire        [7:0] tmp;
  wire        [1:0] memtoreg, regdst;
  wire	      branch,
              pcsrc, zero,
              alusrc, regwrite, jump;
  wire [2:0]  alucontrol;
  
  assign r = aluout[7:0];

  controller c(instr[15:13], instr[3:0], zero,
                memtoreg[1:0], memwrite, pcsrc,
               alusrc,  regdst[1:0], regwrite, jump,
               alucontrol);
  datapath dp(clk, reset,  memtoreg[1:0], pcsrc,
              alusrc,  regdst[1:0], regwrite, jump,
              alucontrol,
              zero, pc, instr,
              aluout, writedata, readdata);
endmodule

module controller(input  [2:0] op, 
                  input  [3:0] funct,
                  input        zero,
                  output [1:0] memtoreg, 
                  output       memwrite,
                  output       pcsrc, alusrc,
                  output [1:0] regdst, 
         	  output       regwrite,
                  output       jump,
                  output [2:0] alucontrol);

  wire [1:0] aluop;
  wire       branch;

  maindec md(op,  memtoreg[1:0], memwrite, branch,
             alusrc,  regdst[1:0], regwrite, jump,
             aluop);
  aludec  ad(funct, aluop, alucontrol);

  assign pcsrc = branch & zero;
endmodule

module maindec(input  [2:0] op,
               output [1:0] memtoreg, 
      	       output	    memwrite,
               output       branch, alusrc,
               output [1:0] regdst, 	
	       output       regwrite,
               output       jump,
               output [1:0] aluop);

  reg [10:0] controls;

  assign {regwrite, regdst[1:0], alusrc,
          branch, memwrite,
          memtoreg[1:0] , jump, aluop} = controls;

  always @(*)
    case(op)
      3'b000: controls <= 11'b10100000000; //Rtype
      3'b100: controls <= 11'b10010001011; //LW
      3'b101: controls <= 11'b00010100011; //SW
      3'b111: controls <= 11'b10010000011; //ADDI
      3'b110: controls <= 11'b00001000001; //BEQ
      3'b010: controls <= 11'b00000000100; //J
      3'b011: controls <= 11'b11000010100; //Jal
      3'b001: controls <= 11'b10010000010; //slti
      default:controls <= 11'bxxxxxxxxxxx; //???
    endcase
endmodule

module aludec(input      [3:0] funct,
              input      [1:0] aluop,
              output reg [2:0] alucontrol);

  always @(*)
    case(aluop)
      2'b11: alucontrol <= 3'b000;  // add
      2'b01: alucontrol <= 3'b001;  // sub
      2'b10: alucontrol <= 3'b100;  // slti
      default: case(funct)          // RTYPE
          4'b0000: alucontrol <= 3'b000; // ADD
          4'b0001: alucontrol <= 3'b001; // SUB
          4'b0010: alucontrol <= 3'b010; // AND
          4'b0011: alucontrol <= 3'b011; // OR
          4'b0100: alucontrol <= 3'b100; // SLT
          default:   alucontrol <= 3'bxxx; // ???
        endcase
    endcase
endmodule

module datapath(input         clk, reset,
                input         [1:0] memtoreg, 
                input	      pcsrc,
                input         alusrc, 
                input   [1:0] regdst,
                input         regwrite, jump,
                input  [2:0]  alucontrol,
                output        zero,
                output [15:0] pc,
                input  [15:0] instr,
                output [15:0] aluout, writedata,
                input  [15:0] readdata);

  wire [2:0]  writereg;
  wire [15:0] pcnext, pcnextbr, pcplus2, pcbranch;
  wire [15:0] signimm, signimmsh;
  wire [15:0] srca, srcb;
  wire [15:0] result;

//-------------------------------------------------------------------------------//
  // next PC logic
  flopr #(16) pcreg(clk, reset, pcnext, pc);
  adder       pcadd1(pc, 16'b10, pcplus2);
  sl2         immsh(signimm, signimmsh);
  adder       pcadd2(pcplus2, signimmsh, pcbranch);
  mux2 #(16)  pcbrmux(pcplus2, pcbranch, pcsrc,
                      pcnextbr);
  mux2 #(16)  pcmux(pcnextbr, {pcplus2[15:14], 
                    instr[12:0], 1'b0}, 
                    jump, pcnext);

  // register file logic
  regfile     rf(clk, regwrite, instr[12:10],
                 instr[9:7], writereg,
                 result, srca, writedata);
  mux4 #(3)   wrmux(instr[9:7], instr[6:4], 
                     regdst[1:0], writereg);
  mux4 #(16)  resmux(aluout, readdata,
                     memtoreg[1:0], result);
  signext     se(instr[6:0], signimm);

  // ALU logic
  mux2 #(16)  srcbmux(writedata, signimm, alusrc,
                      srcb);
  alu         alu(srca, srcb, alucontrol,
                  aluout, zero);
endmodule


//-----------------------------------------------------------------------------------------------------------------------------------------------------------------------
module rategen(
 input clk,rst,
 output cy
 );
 //Generate 1 clock wide pulse on output CY
reg [31:0] Q;
always @(posedge clk)
begin
 if (rst | cy)
 Q <= 0;
 else
 Q <= Q + 1;
end
assign cy = (Q == 100000000);
//assign cy = (Q == 4);
endmodule 
//------------------------------------------------
// top.v
// Top level system including MIPS and memories
//------------------------------------------------
module top(input         clk, reset, 
           output [15:0] writedata, dataadr, 
           output        memwrite,
	        output [7:0]  r);
  rategen rg(clk, reset, cy);
  wire [15:0] pc, instr, readdata;
  // instantiate processor and memories
  mips mips(cy, reset, pc, instr, memwrite, dataadr, writedata, readdata, r);
  imem imem(pc[6:1], instr);
  dmem dmem(cy, memwrite, dataadr, writedata, readdata);
endmodule

	
				
			
