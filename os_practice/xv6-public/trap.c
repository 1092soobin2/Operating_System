#include "types.h"
#include "defs.h"
#include "param.h"
#include "memlayout.h"
#include "mmu.h"
#include "proc.h"
#include "x86.h"
#include "traps.h"
#include "spinlock.h"

// Interrupt descriptor table (shared by all CPUs).
struct gatedesc idt[256];
extern uint vectors[];  // in vectors.S: array of 256 entry pointers
struct spinlock tickslock;
uint ticks;

void
tvinit(void)
{
  int i;

  for(i = 0; i < 256; i++)
    SETGATE(idt[i], 0, SEG_KCODE<<3, vectors[i], 0);
  SETGATE(idt[T_SYSCALL], 1, SEG_KCODE<<3, vectors[T_SYSCALL], DPL_USER);
//  SETGATE(idt[T_PROJECT01_2], 1, SEG_KCODE<<3, vectors[T_PROJECT01_2], DPL_USER);
  SETGATE(idt[128], 1, SEG_KCODE<<3, vectors[128], DPL_USER);

  initlock(&tickslock, "time");
}

void
idtinit(void)
{
  lidt(idt, sizeof(idt));
}

//PAGEBREAK: 41

void controlTimerInt (void);

void
trap(struct trapframe *tf)
{
  if(tf->trapno == T_SYSCALL){
    if(myproc()->killed)
      exit();
    myproc()->tf = tf;
    syscall();
    if(myproc()->killed)
      exit();
    return;
  }

  // Project01_2
  if(tf->trapno == T_PROJECT01_2) {
	  cprintf("user interrupt 128 called!\n");
	  exit();
  }

  switch(tf->trapno){
  case T_IRQ0 + IRQ_TIMER:
    if(cpuid() == 0){
      acquire(&tickslock);
      ticks++;
      wakeup(&ticks);
      release(&tickslock);
    }
    lapiceoi();
    break;
  case T_IRQ0 + IRQ_IDE:
    ideintr();
    lapiceoi();
    break;
  case T_IRQ0 + IRQ_IDE+1:
    // Bochs generates spurious IDE1 interrupts.
    break;
  case T_IRQ0 + IRQ_KBD:
    kbdintr();
    lapiceoi();
    break;
  case T_IRQ0 + IRQ_COM1:
    uartintr();
    lapiceoi();
    break;
  case T_IRQ0 + 7:
  case T_IRQ0 + IRQ_SPURIOUS:
    cprintf("cpu%d: spurious interrupt at %x:%x\n",
            cpuid(), tf->cs, tf->eip);
    lapiceoi();
    break;

  //PAGEBREAK: 13
  default:
    if(myproc() == 0 || (tf->cs&3) == 0){
      // In kernel, it must be our mistake.
      cprintf("unexpected trap %d from cpu %d eip %x (cr2=0x%x)\n",
              tf->trapno, cpuid(), tf->eip, rcr2());
      panic("trap");
    }
    // In user space, assume process misbehaved.
    cprintf("pid %d %s: trap %d err %d on cpu %d "
            "eip 0x%x addr 0x%x--kill proc\n",
            myproc()->pid, myproc()->name, tf->trapno,
            tf->err, cpuid(), tf->eip, rcr2());
    myproc()->killed = 1;
  }

  // Force process exit if it has been killed and is in user space.
  // (If it is still executing in the kernel, let it keep running
  // until it gets to the regular system call return.)
  if(myproc() && myproc()->killed && (tf->cs&3) == DPL_USER)
    exit();

//   // Force process to give up CPU on clock tick.
//   // If interrupts were on while locks held, would need to check nlock.
//   if(myproc() && myproc()->state == RUNNING &&
//      tf->trapno == T_IRQ0+IRQ_TIMER)
//     yield();
	if(myproc() && myproc()->state == RUNNING &&
	 tf->trapno == T_IRQ0+IRQ_TIMER)
	 	controlTimerInt();

  // Check if the process has been killed since we yielded
  if(myproc() && myproc()->killed && (tf->cs&3) == DPL_USER)
    exit();
}



#ifdef FCFS_SCHED
void controlTimerInt(void) {

  mycpu()->prev_pid = myproc()->pid;

	acquire(&tickslock);
	// force quit if 200 ticks exceed
	if ((ticks - myproc()->start_tick) >= 200) { 
		release(&tickslock);
    cprintf("200 ticks elapsed, exit process %d\n", myproc()->pid); 
		exit();
	}
  release(&tickslock);

  yield();
}

#elif MULTILEVEL_SCHED
void controlTimerInt(void) {

	// 1. RR for even pid proc.
	if (myproc()->pid % 2 == 0) {
		yield();
	}
	// 2. FCFS for odd pid proc.
	else {

    mycpu()->prev_pid = myproc()->pid;

		acquire(&tickslock);
    	// force quit if 200 ticks exceed
		if ((ticks - myproc()->start_tick) >= 200) {
      cprintf("200 ticks elapsed, exit process %d\n", myproc()->pid);
			release(&tickslock);
			exit();
		}
		release(&tickslock);

    yield();
	}
}

#elif MLFQ_SCHED
void controlTimerInt(void) {
	
	// monopolize mode
	if (myproc()->is_monopolize == 1) {	}
	// MLFQ mode 
	else {
		// Priority Boost per 200 ticks
		acquire(&tickslock);
		if ((ticks - mycpu()->sched_start_tick) >= 200) {
			boostPriority();
			mycpu()->sched_start_tick = ticks;
		}
		release(&tickslock);

		myproc()->lapse_tick++;

		// 1. RR for L0 proc.
		if (myproc()->lev == 0) {
			// time quantum: 4 ticks
			// if (myproc()->lapse_tick >= 4) {
			// 	myproc()->lapse_tick = 0;
			// 	myproc()->lev = 1;
			// }
      // // RR
      // yield();
      if (myproc()->lapse_tick >= 4) {
        // L0->L1
        myproc()->lev = 1;
        // RR
        yield();
      }
		}
		// 2. Priority Scheduling for L1 proc.
		else if (myproc()->lev == 1) {
			// time quantum: 8 ticks
			if (myproc()->lapse_tick >= 8) {
        // priority decrease
				if (myproc()->priority > 0) {
					myproc()->priority--;
				}
        // RR
        yield();
			}
		}
	}
}

#else 
void controlTimerInt(void) {
	yield();
}

#endif