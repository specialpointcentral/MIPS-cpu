//-------------------------------------------------------
//基于FPEG的SOC设计
// mips.v
// Model of subset of MIPS processor described
// modified by spc
// version: v2.0
// Create time: 2018/07/06
// Latest edit time: 2018/07/08
//-------------------------------------------------------

// top level design for testing
module top #(parameter WIDTH = 32, REGBITS = 5)();
//WIDTH->数据宽度
//REGBITS->寄存器寻址位数
   reg                 clk;
   reg                 reset;
   wire                memread, memwrite;
   wire    [WIDTH-1:0] adr, writedata;
   wire    [WIDTH-1:0] memdata;

   // instantiate devices to be tested
   mips #(WIDTH,REGBITS) dut(clk, reset, memdata, memread, memwrite, adr, writedata);

   // external memory for code and data
   exmemory #(WIDTH) exmem(clk, memwrite, adr, writedata, memdata);

   // initialize test
   initial
      begin
         reset <= 1; # 22; reset <= 0;
      end

   // generate clock to sequence tests
   always
      begin
         clk <= 1; # 5; clk <= 0; # 5;
      end

   always@(negedge clk)
      begin
         if(memwrite)
            if(adr == 5 & writedata == 7)
               $display("Simulation completely successful");
            else $display("Simulation failed");
      end
endmodule

// external memory accessed by MIPS
module exmemory #(parameter WIDTH = 32)
                 (clk, memwrite, adr, writedata, memdata);

   input                  clk;
   input                  memwrite;
   input      [WIDTH-1:0] adr, writedata;
   output reg [WIDTH-1:0] memdata;

   reg  [31:0] RAM [31:0];
   wire [31:0] word;

   initial
      begin
         $readmemb("C:/Users/huqi1/Desktop/memfile.dat",RAM);
      end

   // read and write bytes from 32-bit word
   always @(posedge clk)
		if(memwrite)//写入--高电平有效
			RAM[adr>>2] <= writedata;
	assign word =RAM[adr>>2];
	always @(*)
		memdata <=word;
endmodule

// simplified MIPS processor
module mips #(parameter WIDTH = 32, REGBITS = 5)
             (input              clk, reset, 
              input  [WIDTH-1:0] memdata, 
              output             memread, memwrite, 
              output [WIDTH-1:0] adr, writedata);

   wire [31:0] instr;
   wire        zero, alusrca, memtoreg, iord, pcen, regwrite;
   wire [1:0]  pcsource, alusrcb,regdst,memselect;
   wire        irwrite, pcwritefromaluc, opRtype;
   wire [2:0]  aluop, alucont;
   wire [WIDTH-1:0] writedatas;

   controller  cont(clk, reset, instr[31:26], zero, pcwritefromaluc, memread, memwrite, 
                    alusrca, memtoreg, iord, pcen, regwrite,
                    pcsource, alusrcb, aluop, regdst, irwrite, memselect);
   alucontrol  ac(aluop, instr[5:0], alucont, pcwritefromaluc, opRtype);
   datapath    #(WIDTH, REGBITS) 
               dp(clk, reset, opRtype, memdata, alusrca, memtoreg, iord, pcen,
                  regwrite, pcsource, alusrcb, regdst, irwrite, alucont,
                  zero, instr, adr, writedatas);
   MMRselect   #(WIDTH) mms(writedatas,memselect,writedata);
endmodule

module controller(input clk, reset, 
                  input      [5:0] op, 
                  input            zero, 
                  input            pcwritefromaluc,
                  output reg       memread, memwrite, alusrca, memtoreg, iord, 
                  output           pcen, 
                  output reg       regwrite,
                  output reg [1:0] pcsource, alusrcb, 
                  output reg [2:0] aluop, 
                  output reg [1:0] regdst,
                  output reg       irwrite,
                  output reg [1:0] memselect);

   parameter   FETCH   =  5'd1;
   parameter   DECODE  =  5'd2;
   parameter   MEMADR  =  5'd3;
   parameter   LWRD    =  5'd4;
   parameter   LWWR    =  5'd5;
   parameter   SBWR    =  5'd6;
   parameter   SHWR    =  5'd7;
   parameter   RTYPEEX =  5'd8;
   parameter   RTYPEWR =  5'd9;
   parameter   BEQEX   =  5'd10;
   parameter   BNEEX   =  5'd11;
   parameter   BEX     =  5'd12;
   parameter   JEX     =  5'd13;
   parameter   ANDIEX  =  5'd14;
   parameter   ANDIWR  =  5'd15;
   parameter   ADDIEX  =  5'd16;
   parameter   ADDIWR  =  5'd17;
   parameter   JALEX   =  5'd18;
   parameter   JALWR   =  5'd19;
   parameter   LUIEX   =  5'd20;
   parameter   LUIWR   =  5'd21;
   parameter   ORIEX   =  5'd22;
   parameter   ORIWR   =  5'd23;

   //op code
   parameter   LW      =  6'b100011;
   parameter   SB      =  6'b101000;
   parameter   RTYPE   =  6'b0;
   parameter   BEQ     =  6'b000100;
   parameter   J       =  6'b000010;
   parameter   ANDI    =  6'b001100;
   parameter   ADDI    =  6'b001000;
   parameter   BNE     =  6'b000101;
   parameter   JAL     =  6'b000011;
   parameter   LUI     =  6'b001111;
   parameter   SH      =  6'b101001;
   parameter   ORI     =  6'b001101;

   reg [4:0] state, nextstate;
   reg       pcwrite, pcwritecond, pcbnecond;

   // state register
   always @(posedge clk)
      if(reset) state <= FETCH;
      else state <= nextstate;

   // next state logic
   always @(*)
      begin
         case(state)
            FETCH:  nextstate <= DECODE;
            DECODE:  case(op)
                        SB:      nextstate <= MEMADR;
                        LW:      nextstate <= MEMADR;
                        SH:      nextstate <= MEMADR;
                        RTYPE:   nextstate <= RTYPEEX;
                        BEQ:     nextstate <= BEX;
                        BNE:     nextstate <= BEX;
                        LUI:     nextstate <= LUIEX;
                        ANDI:    nextstate <= ANDIEX;
                        ADDI:    nextstate <= ADDIEX;
                        JAL:     nextstate <= JALEX;
                        J:       nextstate <= JEX;
                        ORI:     nextstate <= ORIEX;
                        default: nextstate <= FETCH; // should never happen
                     endcase
            MEMADR:  case(op)
                        LW:      nextstate <= LWRD;
                        SB:      nextstate <= SBWR;
                        SH:      nextstate <= SHWR;
                        default: nextstate <= FETCH; // should never happen
                     endcase
            BEX:    case(op)
                        BEQ:    nextstate <= BEQEX;
                        BNE:    nextstate <= BNEEX;
                    endcase
            LWRD:    nextstate <= LWWR;
            LWWR:    nextstate <= FETCH;
            SBWR:    nextstate <= FETCH;
            SHWR:    nextstate <= FETCH;
            RTYPEEX: nextstate <= RTYPEWR;
            RTYPEWR: nextstate <= FETCH;
            BEQEX:   nextstate <= FETCH;
            BNEEX:   nextstate <= FETCH;
            ANDIEX:  nextstate <= ANDIWR;
            ANDIWR:  nextstate <= FETCH;
            ADDIEX:  nextstate <= ADDIWR;
            ADDIWR:  nextstate <= FETCH;
            JALEX:   nextstate <= JALWR;
            JALWR:   nextstate <= FETCH;
            LUIEX:   nextstate <= LUIWR;
            LUIWR:   nextstate <= FETCH;
            JEX:     nextstate <= FETCH;
            ORIEX:   nextstate <= ORIWR;
            ORIWR:   nextstate <= FETCH;
            default: nextstate <= FETCH; // should never happen
         endcase
      end

   always @(*)
      begin
            // set all outputs to zero, then conditionally assert just the appropriate ones
            irwrite <= 0;
            pcwrite <= 0; pcwritecond <= 0;
            regwrite <= 0; regdst <= 2'b00;
            memread <= 0; memwrite <= 0;
            alusrca <= 0; alusrcb <= 2'b00; aluop <= 3'b000;
            pcsource <= 2'b00;
            pcbnecond <= 0;//bne condition
            iord <= 0; memtoreg <= 0;memselect<=2'b00;
            case(state)
               FETCH: 
                  begin
                     memread <= 1; 
                     irwrite <= 1; 
                     alusrcb <= 2'b01; 
                     pcwrite <= 1;
                     aluop   <= 3'b001;
                  end
               DECODE: alusrcb <= 2'b11;
               MEMADR:
                  begin
                     alusrca <= 1;
                     alusrcb <= 2'b10;
                     aluop   <= 3'b001;//add
                  end
               LWRD:
                  begin
                     memread <= 1;//允许读
                     iord    <= 1;//adrmux=1
                  end
               LWWR:
                  begin
                     regwrite <= 1;//允许寄存器写
                     memtoreg <= 1;//wdmux=1, regdst=0已赋值
                  end
               SBWR:
                  begin
                     memwrite <= 1;
                     iord     <= 1;//adrmux=1
                     memselect<= 2;//MMRselect=2
                  end
                SHWR:
                  begin
                     memwrite <= 1;
                     iord     <= 1;//adrmux=1
                     memselect<= 1;//MMRselect=1
                  end
               RTYPEEX: 
                  begin
                     alusrca   <= 1;    // src1mux=1
                     //alusrcb <= 0;    // src2mux=0
                     aluop     <= 3'b000;
                  end
               RTYPEWR:
                  begin
                     regdst     <= 1; // regmux=1
                     regwrite   <= 1;
                     //memtoreg <= 0; // wdmux=0
                  end
               BEX:
                  begin
                     //alusrca  <= 0;   // src1mux=0
                     alusrcb  <= 3;     // src2mux=3
                     aluop    <= 3'b001;// add
                  end
               BEQEX:
                  begin
                     alusrca     <= 2'b01;
                     //alusrcb   <= 0;      // src2mux=0
                     aluop       <= 3'b001; // add
                     pcwritecond <= 1;
                     //pcbnecond <= 0;      //bne condition
                     pcsource    <= 2'b01;  // pcmux=1
                  end
               BNEEX:
                  begin
                     alusrca     <= 2'b01;
                     //alusrcb   <= 0;      // src2mux=0
                     aluop       <= 3'b001; // add
                     pcwritecond <= 1;
                     pcbnecond   <= 1;      //bne condition
                     pcsource    <= 2'b01;  // pcmux=1
                  end
               ANDIEX:
                   begin
                     alusrca  <= 1;     // src1mux=1
                     alusrcb  <= 2;     // src2mux=2
                     aluop    <= 3'b011;// and
                   end
               ANDIWR:
                   begin
                     //regdst   <= 0;   // regmux=0
                     regwrite   <= 1;
                     memtoreg   <= 0;   // wdmux=0
                   end
               ORIEX:
                   begin
                     alusrca  <= 1;     // src1mux=1
                     alusrcb  <= 2;     // src2mux=2
                     aluop    <= 3'b110;// or
                   end
               ORIWR:
                   begin
                     //regdst   <= 0;   // regmux=0
                     regwrite   <= 1;
                     memtoreg   <= 0;   // wdmux=0
                   end
               ADDIEX:
                   begin
                     alusrca  <= 1;     // src1mux=1
                     alusrcb  <= 2;     // src2mux=2
                     aluop    <= 3'b001;// add
                   end
               ADDIWR:
                   begin
                     //regdst   <= 0;   // regmux=0
                     regwrite   <= 1;
                     //memtoreg <= 0;   // wdmux=0
                   end
               JALEX:
                   begin
                     alusrca  <= 0;     // src1mux=0
                     alusrcb  <= 1;     // src2mux=1
                     aluop    <= 3'b001;// add
                     pcsource <= 2;     //pcmux=2
                     pcwrite  <= 1;
                   end
               JALWR:
                   begin
                     regdst     <= 2;   // regmux=2
                     regwrite   <= 1;
                     //memtoreg <= 0;   // wdmux=0
                   end
               LUIEX:
                   begin
                     alusrcb  <= 2;     // src2mux=2
                     aluop    <= 3'b111;// <<<16
                   end
               LUIWR:
                   begin
                     regdst     <= 0;   // regmux=0
                     regwrite   <= 1;
                     //memtoreg <= 0;   // wdmux=0
                   end
               JEX:
                  begin
                     pcwrite  <= 1;
                     pcsource <= 3'b10;// pcmux=2
                  end
         endcase
      end
   assign pcen = pcwrite | pcwritefromaluc | (pcwritecond & (pcbnecond ? ~zero: zero)); // program counter enable
endmodule

module alucontrol(input      [2:0] aluop, 
                  input      [5:0] funct, 
                  output reg [2:0] alucont,
                  output reg pcwritefromaluc, opRtype);

   always @(*)
    begin
      pcwritefromaluc <= 0; // pc not write!
      opRtype <= 0;
      case(aluop)
         3'b000: 
         begin
          opRtype <= 1;
          case(funct)       // R-Type instructions
              6'b100000: alucont <= 3'b010; // add (for add)
              6'b100010: alucont <= 3'b110; // subtract (for sub)
              6'b000000: alucont <= 3'b001; // sll
              6'b000010: alucont <= 3'b011; // srl
              6'b001000: 
              begin 
                  alucont <= 3'b010;    // jr only add
                  pcwritefromaluc <= 1; // pc write!
              end
              6'b100101: alucont<= 3'b100;  //or
              default:   alucont <= 3'b101; // should never happen
            endcase
         end
          3'b001: alucont <= 3'b010; // add
          3'b010: alucont <= 3'b110; // sub
          3'b011: alucont <= 3'b000; // and
          3'b100: alucont <= 3'b001; // sll
          3'b101: alucont <= 3'b011; // srl
          3'b110: alucont <= 3'b100; // or
          3'b111: alucont <= 3'b111; // <<<16
      endcase
    end
endmodule

module MMRselect #(parameter WIDTH = 32)
                  (input [WIDTH-1:0]        memdata,
                   input [1:0]              select,
                   output reg [WIDTH-1:0]   writedata);
    //this part is use to select bits
    always@(*)
      case(select)
         2'b00: writedata <= memdata;
         2'b01: writedata <= memdata & 'b1111_1111_1111_1111;
         2'b10: writedata <= memdata & 'b1111_1111;
      endcase
endmodule

module datapath #(parameter WIDTH = 32, REGBITS = 5)
                 (input              clk, reset, opRtype,
                  input  [WIDTH-1:0] memdata, 
                  input              alusrca, memtoreg, iord, pcen, regwrite,
                  input  [1:0]       pcsource, alusrcb, regdst,
                  input              irwrite, 
                  input  [2:0]       alucont, 
                  output             zero, 
                  output [31:0]      instr, 
                  output [WIDTH-1:0] adr, writedata);

   // the size of the parameters must be changed to match the WIDTH parameter
   parameter CONST_ZERO = 32'b0;
   parameter CONST_FOUR = 32'd4;

   wire [REGBITS-1:0] ra1, ra2, wa;
   wire [WIDTH-1:0]   pc, nextpc, md, rd1, rd2, wd, a, src1, src2, aluresult,
                          aluout, constx4, pcconstx4, atomux;

   // shift left constant field by 2
   assign pcconstx4 = {pc[31:28],instr[WIDTH-7:0],2'b00};
   assign constx4   = {{14{instr[WIDTH-17]}},instr[WIDTH-17:0],2'b00};

   // register file address fields
   assign ra1 = instr[REGBITS+20:21];
   assign ra2 = instr[REGBITS+15:16];
   assign atomux = opRtype?(instr[10:6] + a):a;

   mux4       #(REGBITS) regmux(instr[REGBITS+15:16], instr[REGBITS+10:11], 
                                5'd31,CONST_ZERO,
                                regdst, wa);

   // independent of bit width, load instruction into four 8-bit registers over four cycles
   flopen     #(32)      ir0(clk, irwrite, memdata[WIDTH-1:0], instr[WIDTH-1:0]);

   // datapath
   flopenr    #(WIDTH)  pcreg(clk, reset, pcen, nextpc, pc);
   flop       #(WIDTH)  mdr(clk, memdata, md);
   flop       #(WIDTH)  areg(clk, rd1, a);	
   flop       #(WIDTH)  wrd(clk, rd2, writedata);
   flop       #(WIDTH)  res(clk, aluresult, aluout);
   mux2       #(WIDTH)  adrmux(pc, aluout, iord, adr);
   mux2       #(WIDTH)  src1mux(pc, atomux, alusrca, src1);
   mux4       #(WIDTH)  src2mux(writedata, CONST_FOUR, {{16{instr[15]}},instr[15:0]}, 
                                constx4, alusrcb, src2);
   mux4       #(WIDTH)  pcmux(aluresult, aluout, pcconstx4, CONST_ZERO, pcsource, nextpc);
   mux2       #(WIDTH)  wdmux(aluout, md, memtoreg, wd);
   regfile    #(WIDTH,REGBITS) rf(clk, regwrite, ra1, ra2, wa, wd, reset, rd1, rd2);
   alu        #(WIDTH) alunit(src1, src2, alucont, aluresult);
   zerodetect #(WIDTH) zd(aluresult, zero);
endmodule

module alu #(parameter WIDTH = 32)
            (input      [WIDTH-1:0] a, b, 
             input      [2:0]       alucont, 
             output reg [WIDTH-1:0] result);
/*
   wire     [WIDTH-1:0] b2, sum;

   assign b2 = alucont[2] ? ~b:b; 
   assign sum = a + b2 + alucont[2];

   // slt should be 1 if most significant bit of sum is 1
   assign slt = sum[WIDTH-1];

   always@(*)
      case(alucont[1:0])
         2'b00: result <= a & b;
         2'b01: result <= a | b;
         2'b10: result <= sum;
         2'b11: result <= slt;
      endcase
*/
    always@(*)
        case(alucont)
            3'b010: result <= a + b;    //add & sub
            3'b110: result <= a - b;    //add & sub
            3'b000: result <= a & b;    //and
            3'b001: result <= b << a;   //sll
            3'b011: result <= b >> a;   //srl
            3'b100: result <= a | b;    //or
            3'b111: result <= b << 16;
        endcase
endmodule

module regfile #(parameter WIDTH = 32, REGBITS = 5)
                (input                clk, 
                 input                regwrite, 
                 input  [REGBITS-1:0] ra1, ra2, wa, 
                 input  [WIDTH-1:0]   wd, 
                 input                reset,
                 output [WIDTH-1:0]   rd1, rd2);

   reg  [WIDTH-1:0] RAM [(1<<REGBITS)-1:0];
   integer i;
	 always @(posedge clk)
		if (reset) 
			// set all registers to 0
			for (i = 0; i < (1<<REGBITS); i = i + 1)
				RAM[i] <= 0;

   // three ported register file
   // read two ports combinationally
   // write third port on rising edge of clock
   // register 0 hardwired to 0
   always @(posedge clk)
      if (regwrite) RAM[wa] <= wd;	

   assign rd1 = ra1 ? RAM[ra1] : 0;
   assign rd2 = ra2 ? RAM[ra2] : 0;
endmodule

module zerodetect #(parameter WIDTH = 32)
                   (input [WIDTH-1:0] a, 
                    output            y);

   assign y = (a==0);
endmodule	

module flop #(parameter WIDTH = 32)
             (input                  clk, 
              input      [WIDTH-1:0] d, 
              output reg [WIDTH-1:0] q);

   always @(posedge clk)
      q <= d;
endmodule

module flopen #(parameter WIDTH = 32)
               (input                  clk, en,
                input      [WIDTH-1:0] d, 
                output reg [WIDTH-1:0] q);

   always @(posedge clk)
      if (en) q <= d;
endmodule

module flopenr #(parameter WIDTH = 32)
                (input                  clk, reset, en,
                 input      [WIDTH-1:0] d, 
                 output reg [WIDTH-1:0] q);
 
   always @(posedge clk)
      if      (reset) q <= 0;
      else if (en)    q <= d;
endmodule

module mux2 #(parameter WIDTH = 32)
             (input  [WIDTH-1:0] d0, d1, 
              input              s, 
              output [WIDTH-1:0] y);

   assign y = s ? d1 : d0; 
endmodule

module mux4 #(parameter WIDTH = 32)
             (input      [WIDTH-1:0] d0, d1, d2, d3,
              input      [1:0]       s, 
              output reg [WIDTH-1:0] y);

   always @(*)
      case(s)
         2'b00: y <= d0;
         2'b01: y <= d1;
         2'b10: y <= d2;
         2'b11: y <= d3;
      endcase
endmodule
