module cacherand
  #(parameter NUMWAYS = 4, SETLEN = 9, OFFSETLEN = 5, NUMLINES = 128) (
  input  logic                clk, 
  input  logic                reset,
  input  logic                FlushStage,
  input  logic                CacheEn,         // Enable the cache memory arrays.  Disable hold read data constant
  input  logic [NUMWAYS-1:0]  HitWay,          // Which way is valid and matches PAdr's tag
  input  logic [NUMWAYS-1:0]  ValidWay,        // Which ways for a particular set are valid, ignores tag
  input  logic [SETLEN-1:0]   CacheSetData,    // Cache address, the output of the address select mux, NextAdr, PAdr, or FlushAdr
  input  logic [SETLEN-1:0]   CacheSetTag,     // Cache address, the output of the address select mux, NextAdr, PAdr, or FlushAdr
  input  logic [SETLEN-1:0]   PAdr,            // Physical address 
  input  logic                LRUWriteEn,      // Update the LRU state
  input  logic                SetValid,        // Set the dirty bit in the selected way and set
  input  logic                ClearValid,      // Clear the dirty bit in the selected way and set
  input  logic                InvalidateCache, // Clear all valid bits
  output logic [NUMWAYS-1:0]  VictimWay        // LRU selects a victim to evict
);

  localparam                           LOGNUMWAYS = $clog2(NUMWAYS);

  logic [NUMWAYS-2:0]                  LRUMemory [NUMLINES-1:0];
  logic [NUMWAYS-2:0]                  CurrLRU;
  logic [NUMWAYS-2:0]                  NextLRU;
  logic [LOGNUMWAYS-1:0]               HitWayEncoded, Way;
  logic [NUMWAYS-2:0]                  WayExpanded;
  logic                                AllValid;
  
  genvar                               row;

  /* verilator lint_off UNOPTFLAT */
  // Rose: For some reason verilator does not like this.  I checked and it is not a circular path.
  logic [NUMWAYS-2:0]                  LRUUpdate;
  logic [LOGNUMWAYS-1:0] Intermediate [NUMWAYS-2:0];
  logic [3:0] current; 
  /* verilator lint_on UNOPTFLAT */

  logic [NUMWAYS-1:0] FirstZero;
  logic [LOGNUMWAYS-1:0] FirstZeroWay;
  logic [LOGNUMWAYS-1:0] VictimWayEnc;

  binencoder #(NUMWAYS) hitwayencoder(HitWay, HitWayEncoded);

  assign AllValid = &ValidWay;

  ///// Update replacement bits.
  // coverage off
  // Excluded from coverage b/c it is untestable without varying NUMWAYS.
  function integer log2 (integer value);
    int val;
    val = value;
    for (log2 = 0; val > 0; log2 = log2+1)
      val = val >> 1;
    return log2;
  endfunction // log2
  // coverage on

  // On a miss we need to ignore HitWay and derive the new replacement bits with the VictimWay.
  mux2 #(LOGNUMWAYS) WayMuxEnc(HitWayEncoded, VictimWayEnc, SetValid, Way);

  // bit duplication
  // expand HitWay as HitWay[3], {{2}{HitWay[2]}}, {{4}{HitWay[1]}, {{8{HitWay[0]}}, ...
  for(row = 0; row < LOGNUMWAYS; row++) begin
    localparam integer DuplicationFactor = 2**(LOGNUMWAYS-row-1);
    localparam StartIndex = NUMWAYS-2 - DuplicationFactor + 1;
    localparam EndIndex = NUMWAYS-2 - 2 * DuplicationFactor + 2;
    assign WayExpanded[StartIndex : EndIndex] = {{DuplicationFactor}{Way[row]}};
  end

  genvar               node;
  assign LRUUpdate[NUMWAYS-2] = '1;
  for(node = NUMWAYS-2; node >= NUMWAYS/2; node--) begin : enables
    localparam ctr = NUMWAYS - node - 1;
    localparam ctr_depth = log2(ctr);
    localparam lchild = node - ctr;
    localparam rchild = lchild - 1;
    localparam r = LOGNUMWAYS - ctr_depth;

    // the child node will be updated if its parent was updated and
    // the Way bit was the correct value.
    // The if statement is only there for coverage since LRUUpdate[root] is always 1.
    if (node == NUMWAYS-2) begin
      assign LRUUpdate[lchild] = ~Way[r];
      assign LRUUpdate[rchild] = Way[r];
    end else begin
      assign LRUUpdate[lchild] = LRUUpdate[node] & ~Way[r];
      assign LRUUpdate[rchild] = LRUUpdate[node] & Way[r];
    end
  end

  // The root node of the LRU tree will always be selected in LRUUpdate. No mux needed.
  assign NextLRU[NUMWAYS-2] = ~WayExpanded[NUMWAYS-2];
  if (NUMWAYS > 2) mux2 #(1) LRUMuxes[NUMWAYS-3:0](CurrLRU[NUMWAYS-3:0], ~WayExpanded[NUMWAYS-3:0], LRUUpdate[NUMWAYS-3:0], NextLRU[NUMWAYS-3:0]);

  // Compute next victim way.
  for(node = NUMWAYS-2; node >= NUMWAYS/2; node--) begin
    localparam t0 = 2*node - NUMWAYS;
    localparam t1 = t0 + 1;
    assign Intermediate[node] = CurrLRU[node] ? Intermediate[t0] : Intermediate[t1];
  end
  for(node = NUMWAYS/2-1; node >= 0; node--) begin
    localparam int0 = (NUMWAYS/2-1-node)*2;
    localparam int1 = int0 + 1;
    assign Intermediate[node] = CurrLRU[node] ? int1[LOGNUMWAYS-1:0] : int0[LOGNUMWAYS-1:0];
  end
  priorityonehot #(NUMWAYS) FirstZeroEncoder(~ValidWay, FirstZero);
  binencoder #(NUMWAYS) FirstZeroWayEncoder(FirstZero, FirstZeroWay);
  mux2 #(LOGNUMWAYS) VictimMux(FirstZeroWay, current, AllValid, VictimWayEnc);
  decoder #(LOGNUMWAYS) decoder (VictimWayEnc, VictimWay);
endmodule

module LFSR(parameter NUMWAYS)(input clk, rst, output [NUMWAYS - 1:0] current);
  logic [NUMWAYS - 1:0] next; 
  logic en; 
  flopenl #(NUMWAYS) state(clk, rst, en, next, 4'b0010, current);

  switch (NUMWAYS)
    2:
      assign next[1] = current[2] ^ current[0];
      assign next[0] = current[1];
      assign en = '1;
    4:
      assign next[3] = current[3] ^ current[0];
      assign next[2:0] = current[3:1];
      assign en = '1;
    8:
      assign next[7] = current[0] ^ current[2] ^ current[3] ^ current[4];
      assign next[6:0] = current[7:1];
      assign en = '1;
    16:
      assign next[15] = current[1] ^ current[2] ^ current[4] ^ current[5];
      assign next[14:0] = current[15:1];
      assign en = '1;
    32:
      assign next[31] = current[0] ^ current[3] ^ current[5] ^ current[6];
      assign next[30:0] = current[31:1];
      assign en = '1;
    64:
      assign next[63] = current[1] ^ current[2] ^ current[5] ^ current[7];
      assign next[62:0] = current[63:1];
      assign en = '1;
    128:
      assign next[127] = current[3] ^ current[4] ^ current[5] ^ current[6]^ current[8];
      assign next[126:0] = current[127:1];
      assign en = '1;
    default: en = 1'b0;

//hey future karson and hagen, read the paper on LFSR's the bit number for 32 bit and over is smaller, like 128 is supposed to 9 
//its done -Present Karson (as of 4/30/2024)
endmodule 

module flopenl #(parameter WIDTH = 8, parameter type TYPE=logic [WIDTH-1:0]) (
  input  logic clk, load, en,
  input  TYPE d,
  input  TYPE val,
  output TYPE q);

  always_ff @(posedge clk)
    if (load)    q <= val;
    else if (en) q <= d;
endmodule