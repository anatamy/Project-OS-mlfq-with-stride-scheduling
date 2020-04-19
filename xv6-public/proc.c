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
struct proc* high_queue[NPROC];
struct proc* middle_queue[NPROC];
struct proc* low_queue[NPROC];
struct proc* stride_queue[NPROC];
int high_count =-1;
int middle_count =-1;
int low_count =-1;
int tick_count=0;
int stride_count=-1;
int tickPerPri[3] = {1,2,4};
int tickchangePri[2] = {5,10};
int max_tickets =1000;
int mlfq_ticket =1000;
int mlfq_stride =1;
int mlfq_pass=0;
int min_pass=0;

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
  p->priority=0;
  p->clicks=0;
  high_count++;
  high_queue[high_count] = p;
  release(&ptable.lock);
  return 0;

found:
  p->state = EMBRYO;
  p->pid = nextpid++;
  p->priority++;
  p->clicks =0;
  high_count++;
  high_queue[high_count] =p; 
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
    // Scan through table looking for exited children.
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
void
scheduler (void)
{
		// 다음에 실행될 프로세스
	  struct proc *p;
		//iterators
	  int i;
	  int j;
		int it;
		//loop for MLFQ
	  for(;;){
		// Enable interrupts on this processor.
			sti();
			// Loop over process table looking for process to run.
			acquire(&ptable.lock);

			// check we do mlfq or stride
			for(i=0;i<=stride_count;i++)
			{
				// check stride_queue[i] is runnable
				if(stride_queue[i]->state != RUNNABLE)
					continue;
				// find min_pass stirde process
				if(min_pass>stride_queue[i]->pass)
					min_pass=stride_queue[i]->pass;
			}
			// do stride queue
			if(min_pass< mlfq_pass)
			{
				p=stride_queue[i];
				if(p->state != RUNNABLE)
					continue;
				p->pass=p->pass+p->stride;
				min_pass=min_pass+p->stride;
				switchuvm(p);
				p->state = RUNNING; // change process statement => RUNNING
				swtch(&cpu->scheduler, p->context); // change context
				switchkvm();
			}
			// do mlfq queue
			else{
				// priority boost every 100 ticks
				if(tick_count%100==0){
					//priority boost middle_queue
					for(i=0;i<middle_count;i++)
					{
						if(tick_count-middle_queue[i]->last_used>=100){
							p=middle_queue[i];
							high_count++;
							p->priority=0;
							high_queue[high_count] = p;
							/*delete proc from middle_queue*/
							middle_queue[i]=NULL;
							for(j=i;j<=middle_count-1;j++)
								middle_queue[j] = middle_queue[j+1];
							middle_queue[middle_count] = NULL;
							p->clicks = 0;
							middle_count--;
							i--;
							p=0;
						}
					}
					//priority boost low_queue
					for(i=0;i<low_count;i++)
					{
						if(tick_count-low_queue[i]->last_used>=100){
							p=low_queue[i];
							high_count++;
							p->priority=0;
							high_queue[high_count] = p;
							/*delete proc from low_queue*/
							low_queue[i]=NULL;
							for(j=i;j<=low_count-1;j++)
								low_queue[j] = low_queue[j+1];
							low_queue[low_count] = NULL;
							p->clicks = 0;
							low_count--;
							i--;
							p=0;
						}
					}
				}
				// schedule high_queue
				if(high_count!=-1){
					for(i=0;i<=high_count;i++){
						if(high_queue[i]->state != RUNNABLE) // q0 => highest priority queue
							  continue;
					  p=high_queue[i]; // p= process in now
						for(it=0;it<tickPerPri[0];it++){
						  p->clicks++;  // 현재 실행중인 프로세스의 틱 증가
							tick_count++;
							p->last_used=tick_count;
							mlfq_pass=mlfq_pass+mlfq_stride;
							// 실행파트
						  switchuvm(p);
						  p->state = RUNNING; // change process statement => RUNNING
						  swtch(&cpu->scheduler, p->context); // change context
						  switchkvm();
						}
						// 현재 프로세스의 틱이 큐를 바꾸는 상황인지 체크
					  if(p->clicks ==tickchangePri[0]){
						  /*copy proc to lower priority queue*/
							//high_queue -> middle_queue
						  middle_count++; //
							//현재 프로세스의 우선순위 증가
						  p->priority=p->priority+1;
							// 증가된 프로세스를 다음 큐로 복사
						  middle_queue[middle_count] = p;
						  /*delete proc from q0*/
						  high_queue[i]=NULL;
						  for(j=i;j<=high_count-1;j++)
							  high_queue[j] = high_queue[j+1];
						  high_queue[high_count] = NULL;
							p->clicks = 0;
						  high_count--;
					  }
					  p = 0;
					}
				}
				//schedule middle_queue
				if(middle_count!=-1){
					for(i=0;i<=middle_count;i++){
						if(middle_queue[middle_count]->state != RUNNABLE)
							continue;
					  p=middle_queue[i];
						//실행파트
						for(it=0;tickPerPri[1];it++){
							p->clicks++;
							tick_count++;
							p->last_used=tick_count;
							mlfq_pass=mlfq_pass+mlfq_stride;
						  switchuvm(p);
						  p->state = RUNNING;
						  swtch(&cpu->scheduler, p->context);
						  switchkvm();
						}
						//로우큐로 가는 파트
					  if(p->clicks ==tickchangePri[1]){
						  /*copy proc to low_queue*/
						  low_count++;
						  p->priority=p->priority+1;
						  low_queue[low_count] = p;
						  /*delete proc from middle_queue*/
						  middle_queue[i]=NULL;
						  for(j=i;j<=middle_count-1;j++)
							  middle_queue[j] = middle_queue[j+1];
						  middle_queue[middle_count] = NULL;
						  p->clicks = 0;
						  middle_count--;
					  }
					  p = 0;
					}
				}
				// schedule low_queue
				if(low_count!=-1){
					for(i=0;i<=low_count;i++){
						if(low_queue[i]->state != RUNNABLE)
							continue;
						p=low_queue[i];
						//실행파트
						for(it=0;tickPerPri[2];it++){
							p->clicks++;
							tick_count++;
							p->last_used=tick_count;
							mlfq_pass=mlfq_pass+mlfq_stride;
						  switchuvm(p);
						  p->state = RUNNING;
						  swtch(&cpu->scheduler, p->context);
						  switchkvm();
						}
					  p = 0;
					}
				}
			}
			//release lock
			release(&ptable.lock);
    }
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
    if(p->state == SLEEPING && p->chan == chan)
      p->state = RUNNABLE;
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
int
getlev(void)
{
    return myproc() -> priority;
}
int
set_cpu_share(int percent){
	// MLFQ must occupy at least 20%
	struct  proc *p;
	int i;
	int j;
	if(mlfq_ticket - int(max_tickets*percent/100)<=200)
		return -1;
	// take tickets
	else{
		//stide queue에 프로세스를 할당
		p=myproc();
		p->tickets=int(max_tickets*percent/100);
		p->stide=max_tickets/p->tickets;
		p->pass=min_pass;
		stride_count++;
		stride_queue[stride_count]=p;
		// mlfq의 티켓 변동사항 반영
		mlfq_ticket=mlfq_ticket - int(max_tickets*percent/100);
		mlfq_stride=int(max_tickets/mlfq_ticket);
		// mlfq에서 프로세스 제거
		for(i=0;i<=high_count;i++)
		{
			if(high_queue[i]->pid==p->pid){
				high_queue[i]=NULL;
				for(j=i;j<=high_count-1;j++){
					high_queue[j] = high_queue[j+1];
					high_queue[high_count] = NULL;
					high_count--;
				}
				return 0;
			}
		}
	}
		return  0;
}

int getppid(void)
{
    return myproc() -> parent -> pid;

}
