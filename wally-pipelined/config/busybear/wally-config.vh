//////////////////////////////////////////
// busybear-config.vh
//
// Written: David_Harris@hmc.edu 4 January 2021
// Modified: 
//
// Purpose: Specify which features are configured
//          Macros to determine which modes are supported based on MISA
// 
// A component of the Wally configurable RISC-V project.
// 
// Copyright (C) 2021 Harvey Mudd College & Oklahoma State University
//
// Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated documentation
// files (the "Software"), to deal in the Software without restriction, including without limitation the rights to use, copy, 
// modify, merge, publish, distribute, sublicense, and/or sell copies of the Software, and to permit persons to whom the Software 
// is furnished to do so, subject to the following conditions:
//
// The above copyright notice and this permission notice shall be included in all copies or substantial portions of the Software.
//
// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES 
// OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS 
// BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT 
// OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
///////////////////////////////////////////

`define BUILDROOT 0
`define BUSYBEAR 1
`define BUSYBEAR_FIX_READ {'h10000005}
`define BUSYBEAR_TEST_VECTORS "/courses/e190ax/busybear_boot_new/"
// RV32 or RV64: XLEN = 32 or 64
`define XLEN 64

`define MISA (32'h0014112D)
`define A_SUPPORTED ((`MISA >> 0) % 2 == 1)
`define C_SUPPORTED ((`MISA >> 2) % 2 == 1)
`define D_SUPPORTED ((`MISA >> 3) % 2 == 1)
`define F_SUPPORTED ((`MISA >> 5) % 2 == 1)
`define M_SUPPORTED ((`MISA >> 12) % 2 == 1)
`define S_SUPPORTED ((`MISA >> 18) % 2 == 1)
`define U_SUPPORTED ((`MISA >> 20) % 2 == 1)
`define ZCSR_SUPPORTED 1
`define ZCOUNTERS_SUPPORTED 1
`define COUNTERS 31
// N-mode user-level interrupts are depricated per Andrew Waterman 1/13/21
//`define N_SUPPORTED ((MISA >> 13) % 2 == 1)
`define N_SUPPORTED 0

`define M_MODE (2'b11)
`define S_MODE (2'b01)
`define U_MODE (2'b00)

// Microarchitectural Features
`define UARCH_PIPELINED 1
`define UARCH_SUPERSCALR 0
`define UARCH_SINGLECYCLE 0
`define MEM_DCACHE 0
`define MEM_DTIM 1
`define MEM_ICACHE 0
`define MEM_VIRTMEM 0
`define VECTORED_INTERRUPTS_SUPPORTED 1 // Domenico Ottolia 4/15: Support for vectored interrupts in _tvec csrs. Just implemented in src/privileged/trap.sv around line 75. Pretty sure this should be 1.

// Address space
`define RESET_VECTOR 64'h0000000000001000

// Peripheral Addresses
// Peripheral memory space extends from BASE to BASE+RANGE
// Range should be a thermometer code with 0's in the upper bits and 1s in the lower bits

`define BOOTTIMBASE   32'h00000000 //only needs to go from 0x1000 to 0x2FFF, extending to a power of 2
`define BOOTTIMRANGE  32'h00003FFF
`define CLINTBASE     32'h02000000
`define CLINTRANGE    32'h0000FFFF
`define PLICBASE      32'h0C000000
`define PLICRANGE     32'h03FFFFFF
`define UARTBASE      32'h10000000
`define UARTRANGE     32'h00000007
`define VBD0BASE      32'h10001000
`define VBD0RANGE     32'h000001FF
// differing from Imperas' OVPSim by not having a VND0
`define GPIOBASE      32'h20000000 
`define GPIORANGE     32'h000000FF
`define TIMBASE       32'h80000000
`define TIMRANGE      32'h07FFFFFF
// Bus Interface width
`define AHBW 64

// Test modes

// Tie GPIO outputs back to inputs
`define GPIO_LOOPBACK_TEST 0

// Busybear special CSR config to match OVPSim
`define OVPSIM_CSR_CONFIG 1

// Hardware configuration
`define UART_PRESCALE 1

// Interrupt configuration
`define PLIC_NUM_SRC 53
`define PLIC_UART_ID 4

/* verilator lint_off STMTDLY */
/* verilator lint_off WIDTH */

`define TWO_BIT_PRELOAD "../config/busybear/twoBitPredictor.txt"
`define BTB_PRELOAD "../config/busybear/BTBPredictor.txt"
`define BPTYPE "BPGSHARE" // BPGLOBAL or BPTWOBIT or BPGSHARE
