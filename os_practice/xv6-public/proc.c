#include "types.h"
#include "defs.h"
#include "param.h"
#include "memlayout.h"
#include "mmu.h"
#include "x86.h"
#include "proc.h"
#include "spinlock.h"

struct {
  struct spinlock lock;
  struct proc proc[NPROC];
} ptable;

static struct proc *initproc;

int nextpid = 1;
extern void forkret(void);
extern void trapret(void);

static void wakeup1(void *chan);

void
pinit(void)
{
  initlock(&ptable.lock, "ptable");
}

// Must be called with interrupts disabled
int
cpuid() {
  return mycpu()-cpus;
}

// Must be called with interrupts disabled to avoid the caller being
// rescheduled between reading lapicid and running through the loop.
struct cpu*
mycpu(void)
{
  int apicid, i;
  
  if(readeflags()&FL_IF)
    panic("mycpu called with interrupts enabled\n");
  
  apicid = lapicid();
  // APIC IDs are not guaranteed to be contiguous. Maybe we should have
  // a reverse map, or reserve a register to store &cpus[i].
  for (i = 0; i < ncpu; ++i) {
    if (cpus[i].apicid == apicid)
      return &cpus[i];
  }
  panic("unknown apicid\n");
}

// Disable interrupts so that we are not rescheduled
// while reading proc from the cpu structure
struct proc*
myproc(void) {
    struct cpu *c;
    struct proc *p;
    pushcli();
    c = mycpu();
    p = c->proc;
    popcli();
    return p;
}

//PAGEBREAK: 32
// Look in the process table for an UNUSED proc.
// If found, change state to EMBRYO and initialize
// state required to run in the kernel.
// Otherwise return 0.
static struct proc*
allocproc(void)
{
    struct proc *p;
    char *sp;

    acquire(&ptable.lock);

    for(p = ptable.proc; p < &ptable.proc[NPROC]; p++)
    if(p->state == UNUSED)
      goto found;

    release(&ptable.lock);
    return 0;

found:
    p->state = EMBRYO;
    p->pid = nextpid++;

    release(&ptable.lock);

    // Allocate kernel stack.
    if((p->kstack = kalloc()) == 0){
        p->state = UNUSED;
        return 0;
    }
    sp = p->kstack + KSTACKSIZE;

    // Leave room for trap frame.
    sp -= sizeof *p->tf;
    p->tf = (struct trapframe*)sp;

    // Set up new context to start executing at forkret,
    // which returns to trapret.
    sp -= 4;
    *(uint*)sp = (uint)trapret;

    sp -= sizeof *p->context;
    p->context = (struct context*)sp;
    memset(p->context, 0, sizeof *p->context);
    p->context->eip = (uint)forkret;

    // Project02
    // acquire(&tickslock);
    // p->alloc_tick = ticks;
    // release(&tickslock);
	// p->preemption = 0;
	p->start_tick = 0;
	p->lev = 0;
    p->priority = 0;
	p->lapse_tick = 0;
	p->is_monopolize = 0;

    return p;
}

//PAGEBREAK: 32
// Set up first user process.
void
userinit(void)
{
  struct proc *p;
  extern char _binary_initcode_start[], _binary_initcode_size[];

  p = allocproc();
  
  initproc = p;
  if((p->pgdir = setupkvm()) == 0)
    panic("userinit: out of memory?");
  inituvm(p->pgdir, _binary_initcode_start, (int)_binary_initcode_size);
  p->sz = PGSIZE;
  memset(p->tf, 0, sizeof(*p->tf));
  p->tf->cs = (SEG_UCODE << 3) | DPL_USER;
  p->tf->ds = (SEG_UDATA << 3) | DPL_USER;
  p->tf->es = p->tf->ds;
  p->tf->ss = p->tf->ds;
  p->tf->eflags = FL_IF;
  p->tf->esp = PGSIZE;
  p->tf->eip = 0;  // beginning of initcode.S

  safestrcpy(p->name, "initcode", sizeof(p->name));
  p->cwd = namei("/");

  // this assignment to p->state lets other cores
  // run this process. the acquire forces the above
  // writes to be visible, and the lock is also needed
  // because the assignment might not be atomic.
  acquire(&ptable.lock);

  p->state = RUNNABLE;

  release(&ptable.lock);
}

// Grow current process's memory by n bytes.
// Return 0 on success, -1 on failure.
int
growproc(int n)
{
  uint sz;
  struct proc *curproc = myproc();

  sz = curproc->sz;
  if(n > 0){
    if((sz = allocuvm(curproc->pgdir, sz, sz + n)) == 0)
      return -1;
  } else if(n < 0){
    if((sz = deallocuvm(curproc->pgdir, sz, sz + n)) == 0)
      return -1;
  }
  curproc->sz = sz;
  switchuvm(curproc);
  return 0;
}

// Create a new process copying p as the parent.
// Sets up stack to return as if from system call.
// Caller must set state of returned proc to RUNNABLE.
int
fork(void)
{
  int i, pid;
  struct proc *np;
  struct proc *curproc = myproc();

  // Allocate process.
  if((np = allocproc()) == 0){
    return -1;
  }

  // Copy process state from proc.
  if((np->pgdir = copyuvm(curproc->pgdir, curproc->sz)) == 0){
    kfree(np->kstack);
    np->kstack = 0;
    np->state = UNUSED;
    return -1;
  }
  np->sz = curproc->sz;
  np->parent = curproc;
  *np->tf = *curproc->tf;

  // Clear %eax so that fork returns 0 in the child.
  np->tf->eax = 0;

  for(i = 0; i < NOFILE; i++)
    if(curproc->ofile[i])
      np->ofile[i] = filedup(curproc->ofile[i]);
  np->cwd = idup(curproc->cwd);

  safestrcpy(np->name, curproc->name, sizeof(curproc->name));

  pid = np->pid;

  acquire(&ptable.lock);

  np->state = RUNNABLE;

  release(&ptable.lock);

  return pid;
}

// Exit the current process.  Does not return.
// An exited process remains in the zombie state
// until its parent calls wait() to find out it exited.
void
exit(void)
{
  struct proc *curproc = myproc();
  struct proc *p;
  int fd;

  if(curproc == initproc)
    panic("init exiting");

  // Close all open files.
  for(fd = 0; fd < NOFILE; fd++){
    if(curproc->ofile[fd]){
      fileclose(curproc->ofile[fd]);
      curproc->ofile[fd] = 0;
    }
  }
  begin_op();
  iput(curproc->cwd);
  end_op();
  curproc->cwd = 0;

  acquire(&ptable.lock);

  // Parent might be sleeping in wait().
  wakeup1(curproc->parent);

  // Pass abandoned children to init.
  for(p = ptable.proc; p < &ptable.proc[NPROC]; p++){
    if(p->parent == curproc){
      p->parent = initproc;
      if(p->state == ZOMBIE)
        wakeup1(initproc);
    }
  }

  // Jump into the scheduler, never to return.
  curproc->state = ZOMBIE;
  sched();
  panic("zombie exit");
}

// Wait for a child process to exit and return its pid.
// Return -1 if this process has no children.
int
wait(void)
{
  struct proc *p;
  int havekids, pid;
  struct proc *curproc = myproc();
  acquire(&ptable.lock);
  for(;;){
    // Scan through table looking for exited children.w
    havekids = 0;
    for(p = ptable.proc; p < &ptable.proc[NPROC]; p++){
      if(p->parent != curproc)
        continue;
      havekids = 1;
      if(p->state == ZOMBIE){
        // Found one.
        pid = p->pid;
        kfree(p->kstack);
        p->kstack = 0;
        freevm(p->pgdir);
        p->pid = 0;
        p->parent = 0;
        p->name[0] = 0;
        p->killed = 0;
        p->state = UNUSED;
        release(&ptable.lock);
        return pid;
      }
    }

    // No point waiting if we don't have any children.
    if(!havekids || curproc->killed){
      release(&ptable.lock);
      return -1;
    }

    // Wait for children to exit.  (See wakeup1 call in proc_exit.)
    sleep(curproc, &ptable.lock);  //DOC: wait-sleep
  }
}

//PAGEBREAK: 42
// Per-CPU process scheduler.

// Each CPU calls scheduler() after setting itself up.
// Scheduler never returns.  It loops, doing:
//  - choose a process to run
//  - swtch to start running that process
//  - eventually that process transfers control
//      via swtch back to the scheduler.

// Project02
void FCFS(void) __attribute__((noreturn));
void MULTILEVEL(void) __attribute__((noreturn));
void MLFQ(void) __attribute__((noreturn));
void DEFAULT_RR(void) __attribute__((noreturn));

void scheduler(void) {
	#ifdef FCFS_SCHED
	FCFS();
	#elif MULTILEVEL_SCHED
	MULTILEVEL();
	#elif MLFQ_SCHED
	MLFQ();
	#else
	DEFAULT_RR();
	#endif
}

/* FCFS
1. no switched out until termination
2. if proc. isn't terminated or doesn't sleep until 200 ticks, then force to quit
3. if first-come proc. sleeping, then next proc.
4. if first-come proc. wakeup,   then first-come proc.
*/
void FCFS (void) {
    struct proc *p;
    struct cpu *c = mycpu();
    c->proc = 0;              // Make no running process in this cpu
    struct proc *tmp_p;
	c->prev_pid = 0;

    for (;;) {
        // Enable INT on this processor
        sti();		
		
        // Look for process to run
        acquire(&ptable.lock);
        for (p = ptable.proc; p < &ptable.proc[NPROC]; p++) {

			// 1. Find RUNNABLE process
			if (p->state != RUNNABLE) {
				continue;
			}
			
			// 2. Find First-Come && RUNNABLE process
			// Search min pid proc.
			for (tmp_p = ptable.proc; tmp_p < &ptable.proc[NPROC]; tmp_p++) {
				// if (p->state == RUNNABLE) {
				if (tmp_p->state == RUNNABLE) {
					if (p->pid > tmp_p->pid) {
						p = tmp_p;
					}
				}
			}

			// 3. Switch to chosen process.
			c->proc = p;
			switchuvm(p);
			p->state = RUNNING;
			// scheduling start time
			// if (p->start_tick == 0) {
			if (p->pid != c->prev_pid) {		// if new proc. catch CPU
				acquire(&tickslock);
				p->start_tick = ticks;
				release(&tickslock);
			}

            swtch(&(c->scheduler), p->context);

			// 4. Proc. is done
            switchkvm();
            c->proc = 0;
		}
        release(&ptable.lock);
	}
}

/* Multilevel Queue
1. even pid proc      RR	(precede all odd, only RUNNABLE)
2. odd pid proc       FCFS	(low -> high) preemption
*/
void MULTILEVEL(void) {
    struct proc *p;
    struct cpu *c = mycpu();
    c->proc = 0;
    struct proc *tmp_p;
	int is_any_even_proc;
	c->prev_pid = 0;

    for (;;) {

        // Enable INT
        sti();

        // Look for process to run
        acquire(&ptable.lock);
        // 1. RR for even pid proc.
        for (p = ptable.proc; p < &ptable.proc[NPROC]; p++) {

            // 1-1. Find RUNNABLE && even proc.
            if (p->pid % 2 == 1 || p->state != RUNNABLE)
                continue;

            // 1-2. Switch to chosen proc.
            c->proc = p;
            switchuvm(p);
            p->state = RUNNING;

            swtch(&(c->scheduler), p->context);
            switchkvm();

            // 1-3. Proc. is done
            c->proc = 0;
        }
        // even pid proc.s all done
		is_any_even_proc = 0;

        // 2. FCFS for odd pid proc.
        for (p = ptable.proc; p < &ptable.proc[NPROC]; p++) {

			// 2-1. Find RUNNABLE && odd proc.
			if (p->pid % 2 == 0 || p->state != RUNNABLE){
				continue;
			}

            // 2-2. Check if there is some RUNNABLE && even proc.
            for (tmp_p = ptable.proc; tmp_p < &ptable.proc[NPROC]; tmp_p++) {
                if (tmp_p->pid % 2 == 0 && tmp_p->state == RUNNABLE) {
					is_any_even_proc = 1;
					break;
				}
            }
			if (is_any_even_proc == 1) {
				break;
			}

            // 2-3. If there is no even proc.
			// Then, find min pid odd proc.
            for (tmp_p = ptable.proc; tmp_p < &ptable.proc[NPROC]; tmp_p++) {
                if (tmp_p->pid % 2 == 1 && tmp_p->state == RUNNABLE) {
                    if (p->pid > tmp_p->pid) {
                        p = tmp_p;
                    }
                }
            }

            // 2-4. Switch to chosen proc.
            c->proc = p;
            switchuvm(p);
            p->state = RUNNING;
			// FCFS, scheduling start time
			if (p->pid != c->prev_pid) {
				acquire(&tickslock);
				p->start_tick = ticks;
				release(&tickslock);
			}

            swtch(&(c->scheduler), p->context);
            switchkvm();

            // 2-5. Proc. is done
            c->proc = 0;
        }
        release(&ptable.lock);
    }
}

/* MLFQ
TODO: 1. Enable/Disable preemption (should be finished in 1 tick)
2. L0
-RR
-time quantum: 4 ticks


3. L1
-Priority Scheduling
-time quantum: 8 ticks

4. monopolize
-ignore MLFQ scheduling, exclusive use of processor
-password: 2019011449
-If called again, proc. will be L0 and priority 0

assumption: #(CPU) == 1

When a user process is forced to quit, print message

*/
void MLFQ(void) {
	struct proc *p;
	struct cpu *c = mycpu();
	c->proc = 0;
	struct proc *tmp_p;
	int is_any_L0_proc;

	// for priority boost
	acquire(&tickslock);
	c->sched_start_tick = ticks;
	release(&tickslock);	

	for (;;) {

		// Enable INT
		sti();

		// FIXME: 2 Q -> multiple Q
		// Look for process to run
		acquire(&ptable.lock);
		// 1. RR for L0
		for (p = ptable.proc; p < &ptable.proc[NPROC]; p++) {

			// 1-1. Find RUNNABLE && L0 proc.
			if (p->lev != 0 || p->state != RUNNABLE) 
				continue;

			// 1-2. Switch to chosen proc.
			c->proc = p;
			switchuvm(p);
			p->state = RUNNING;
			// time quantum: 4 ticks
			p->lapse_tick = 0;

			swtch(&(c->scheduler), p->context);
			switchkvm();

			// 1-3. Proc. is done
			c->proc = 0;
		}
		// L0 proc. is all done
		is_any_L0_proc = 0;

		// 2. Priority Scheduling for L1
		for (p = ptable.proc; p < &ptable.proc[NPROC]; p++) {

			// 2-1. Find RUNNABLE && L1 proc.
			if (p->lev != 1 || p->state != RUNNABLE) {
				continue;
			}
			
			// 2-2. Check if there is some RUNNABLE && L0 proc.
			for (tmp_p = ptable.proc; tmp_p < &ptable.proc[NPROC]; tmp_p++) {
				if (tmp_p->lev == 0 && tmp_p->state == RUNNABLE) {
					is_any_L0_proc = 1;
					break;
				}
			}
			if (is_any_L0_proc == 1) {
				break;
			}

			// 2-3. If there is no L0 proc.
			// Then, find highest priority L1 proc. 
			for (tmp_p = ptable.proc; tmp_p < &ptable.proc[NPROC]; tmp_p++) {
				if (tmp_p->lev == 1 && tmp_p->state == RUNNABLE) {
					// higher priority
					if (p->priority < tmp_p->priority) {
						p = tmp_p;
					}
					// same priority, then FCFS
					else if (p->priority == tmp_p->priority) {
						if (p->pid > tmp_p->pid) {
							p = tmp_p;
						}
					}
				}
			}

			// 2-4. Switch to chosen proc.
			c->proc = p;
			switchuvm(p);
			p->state = RUNNING;
			// time quantum: 8 ticks
			p->lapse_tick = 0;

			// TODO: Enabling preemption now: Disabling preemption
			swtch(&(c->scheduler), p->context);
			switchkvm();

			// 2-5. Proc. is done
			c->proc = 0;
		}
		release(&ptable.lock);		
	}
}

void DEFAULT_RR (void) {
    struct proc *p;
    struct cpu *c = mycpu();
    c->proc = 0;

    for (;;) {
        // Enable interrupts on this processor.
        sti();

        // Loop over process table looking for process to run.
        acquire(&ptable.lock);
        for (p = ptable.proc; p < &ptable.proc[NPROC]; p++) {
            if (p->state != RUNNABLE)
                continue;

            // Switch to chosen process.  It is the process's job
            // to release ptable.lock and then reacquire it
            // before jumping back to us.
            c->proc = p;
            switchuvm(p);
            p->state = RUNNING;

            swtch(&(c->scheduler), p->context);
            switchkvm();

            // Process is done running for now.
            // It should have changed its p->state before coming back.
            c->proc = 0;
        }
        release(&ptable.lock);

    }
}

/* Syscalls for MLFQ*/
// int getlev(void) {}

// priority: 0 - 10
int setpriority(int pid, int priority) {
	struct proc *p;

	// -2 if priority is n/a
	if (priority < 0 || priority > 10) {
		return -2;
	}

	// 0 if success
	acquire(&ptable.lock);
	for (p = ptable.proc; p < &ptable.proc[NPROC]; p++) {
		// if (p->pid == pid && myproc()->pid == p->parent->pid) {
		if (p->pid == pid) {
			p->priority = priority;
			release(&ptable.lock);
			return 0;
			}
	}
	// -1 if pid doesn't exist ||  pid is not child of myproc()
	// 		not(exist) || not(child)
	// 		not (exist && child)
	release(&ptable.lock);
	return -1;
}

// password: my student number
void monopolize (int password) {

	// Toggle is_monopolize
	// MLFQ mode
	if (myproc()->is_monopolize == 0) {
		// if wrong, force quit
		if (password != 2019011449) {
			cprintf("Wrong password, exit process %d\n", myproc()->pid);
			exit();
		}
		// monopolize mode on
		myproc()->is_monopolize = 1;
	}
	// monopolize mode
	else {
		// monopolize mode off (MLFQ mode)
		myproc()->is_monopolize = 0;
		// if wrong, force quit
		if (password != 2019011449) {
			cprintf("Wrong password, exit process %d\n", myproc()->pid);
			exit();
		}
		// L0
		myproc()->lev = 0;
		myproc()->lapse_tick = 0;
		// priority
		myproc()->priority = 0;
	}
}

/* Priority Boost for MLFQ */
void boostPriority(void) {
	struct proc *p;

	acquire(&ptable.lock);
	for (p = ptable.proc; p < &ptable.proc[NPROC]; p++) {

		p->lev = 0;
		p->lapse_tick = 0;
		
		p->priority = 0;
	}
	release(&ptable.lock);
}

// Enter scheduler.  Must hold only ptable.lock
// and have changed proc->state. Saves and restores
// intena because intena is a property of this
// kernel thread, not this CPU. It should
// be proc->intena and proc->ncli, but that would
// break in the few places where a lock is held but
// there's no process.
void
sched(void)
{
  int intena;
  struct proc *p = myproc();

  if(!holding(&ptable.lock))
    panic("sched ptable.lock");
  if(mycpu()->ncli != 1)
    panic("sched locks");
  if(p->state == RUNNING)
    panic("sched running");
  if(readeflags()&FL_IF)
    panic("sched interruptible");
  intena = mycpu()->intena;
  swtch(&p->context, mycpu()->scheduler);
  mycpu()->intena = intena;
}

//TODO:
// Give up the CPU for one scheduling round.
void
yield(void)
{
  acquire(&ptable.lock);  //DOC: yieldlock
  myproc()->state = RUNNABLE;
  sched();
  release(&ptable.lock);
}

// A fork child's very first scheduling by scheduler()
// will swtch here.  "Return" to user space.
void
forkret(void)
{
  static int first = 1;
  // Still holding ptable.lock from scheduler.
  release(&ptable.lock);

  if (first) {
    // Some initialization functions must be run in the context
    // of a regular process (e.g., they call sleep), and thus cannot
    // be run from main().
    first = 0;
    iinit(ROOTDEV);
    initlog(ROOTDEV);
  }

  // Return to "caller", actually trapret (see allocproc).
}

// Atomically release lock and sleep on chan.
// Reacquires lock when awakened.
void
sleep(void *chan, struct spinlock *lk)
{
  struct proc *p = myproc();
  
  if(p == 0)
    panic("sleep");

  if(lk == 0)
    panic("sleep without lk");

  // Must acquire ptable.lock in order to
  // change p->state and then call sched.
  // Once we hold ptable.lock, we can be
  // guaranteed that we won't miss any wakeup
  // (wakeup runs with ptable.lock locked),
  // so it's okay to release lk.
  if(lk != &ptable.lock){  //DOC: sleeplock0
    acquire(&ptable.lock);  //DOC: sleeplock1
    release(lk);
  }
  // Go to sleep.
  p->chan = chan;
  p->state = SLEEPING;

  sched();

  // Tidy up.
  p->chan = 0;

  // Reacquire original lock.
  if(lk != &ptable.lock){  //DOC: sleeplock2
    release(&ptable.lock);
    acquire(lk);
  }
}

//PAGEBREAK!
// Wake up all processes sleeping on chan.
// The ptable lock must be held.
static void
wakeup1(void *chan)
{
  struct proc *p;

  for(p = ptable.proc; p < &ptable.proc[NPROC]; p++)
    if(p->state == SLEEPING && p->chan == chan) {
      p->state = RUNNABLE;
	//   myproc()->preemption = 1;
	}
}

// Wake up all processes sleeping on chan.
void
wakeup(void *chan)
{
  acquire(&ptable.lock);
  wakeup1(chan);
  release(&ptable.lock);
}

// Kill the process with the given pid.
// Process won't exit until it returns
// to user space (see trap in trap.c).
int
kill(int pid)
{
  struct proc *p;

  acquire(&ptable.lock);
  for(p = ptable.proc; p < &ptable.proc[NPROC]; p++){
    if(p->pid == pid){
      p->killed = 1;
      // Wake process from sleep if necessary.
      if(p->state == SLEEPING)
        p->state = RUNNABLE;
      release(&ptable.lock);
      return 0;
    }
  }
  release(&ptable.lock);
  return -1;
}

//PAGEBREAK: 36
// Print a process listing to console.  For debugging.
// Runs when user types ^P on console.
// No lock to avoid wedging a stuck machine further.
void
procdump(void)
{
  static char *states[] = {
  [UNUSED]    "unused",
  [EMBRYO]    "embryo",
  [SLEEPING]  "sleep ",
  [RUNNABLE]  "runble",
  [RUNNING]   "run   ",
  [ZOMBIE]    "zombie"
  };
  int i;
  struct proc *p;
  char *state;
  uint pc[10];

  for(p = ptable.proc; p < &ptable.proc[NPROC]; p++){
    if(p->state == UNUSED)
      continue;
    if(p->state >= 0 && p->state < NELEM(states) && states[p->state])
      state = states[p->state];
    else
      state = "???";
    cprintf("%d %s %s", p->pid, state, p->name);
    if(p->state == SLEEPING){
      getcallerpcs((uint*)p->context->ebp+2, pc);
      for(i=0; i<10 && pc[i] != 0; i++)
        cprintf(" %p", pc[i]);
    }
    cprintf("\n");
  }
}
