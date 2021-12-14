# RISC-V-Out-of-Order-Processor
A 9 instruction 2-issue RISC-V Out of Order Processor designed as the Honors Final Project for UCLA's M116C Computer Systems Architecture course. 

## Testing Input
To change the instruction memory, find line 20 in fetch.sv and input a string containing the name of the new source file.
Display statements are also left commented out in each module to help with monitoring outputs or Reservation Station and ROB entry values at each stage.

## Hazards
Renaming accounts for WAW and WAR hazards. Other memory hazards are still possible due to the absence of store queues.
