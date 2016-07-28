using CP;

int nTasks  = ...; 
int nProcs = ...;
int nEdges = ...;
int variables = ...;

range Tasks = 1..nTasks;
range Procs = 1..nProcs;
range Edges = 1..nEdges;
range mem_choices = 1..2;
range nvars = 1..variables;

int cc[t in Tasks, p in Procs] = ...;
int snode[e in Edges] = ...;
int tnode[e in Edges] = ...;
int com[e in Edges] = ...;

//diferrent execution of the task according to the data allocation
int var_exec[n in nvars][m in mem_choices] = ...;

//tuple for the data requirements
tuple dat_req {
	int task_id;
	int var_size;
	int var_freq;
	int var_id;
};

//spm info for each proc
tuple spm {
	key int proc;
	int spm_size;
};

{dat_req} data_requirements = ...;
{spm} spm_proc =  ...;

// Create the interval variables for the tasks

//task_new is the new interval which its execution time increased according to the allocation of data in spm or main
dvar interval task_new[t in Tasks];
dvar interval task[t in Tasks];
dvar interval ptask[t in Tasks][p in Procs] optional size cc[t][p];
dvar sequence stask[p in Procs] in all (t in Tasks) ptask[t][p];

//create the interval variables for the data

// create interval for the data of each task
dvar interval data_tasks[t in Tasks]; //data_tasks are the overall tasks which span for all the variable tasks
dvar interval data_tasks_var[n in nvars]; //intervals for each variable
dvar interval pdata_task[n in nvars][m in mem_choices] optional size var_exec[n][m];//optional invervals for the mapping of the data in spm or main memory
//sequence the interval of the data in order to increase the span of the data_task. This increase, with the precedence costraints increase the overall task
dvar sequence sdata_task[t in Tasks] in all (m in mem_choices,n in nvars,d in data_requirements:d.task_id == t && n == d.var_id) pdata_task[n][m];

//execute {
//	cp.param.TimeLimit = 60;
//	cp.param.LogPeriod = 100000;
//	var f = cp.factory; 
//	var phase = f.searchPhase(task); 
//	cp.setSearchPhases(phase);	
//
//}

// the objective
minimize max(t in Tasks) endOf(task_new[t]);

//cumulative function for the number of processors for each task interval
cumulFunction f = sum(t in Tasks) pulse(task[t], 1);

//spm cumulative function for the ptasks which assigned in the spm
//cumulFunction spm_cumul[t in Tasks] = sum(n in nvars, d in data_requirements:d.task_id == t && n == d.var_id) stepAtStart(pdata_task[n][1], d.var_size);
dexpr int spm_usage[t in Tasks]= sum(n in nvars, d in data_requirements:d.task_id == t && n == d.var_id) presenceOf(pdata_task[n][1]) * d.var_size;

subject to {

	//costraint for the data_allocation and the mapping to each processor
	
    // alternative constraints:
    forall(t in Tasks)
      a:alternative(task[t], all(p in Procs) ptask[t][p]);

	// no overlap constraints:
  	forall(p in Procs)
    	b:noOverlap(stask[p]);
    	
    //no overlap in the data_tasks sequence
    forall(t in Tasks)
      c:noOverlap(sdata_task[t]);
   
   	//alternative between data_task_vars and pdata_tasks
   	forall(n in nvars)
   	  d:alternative(data_tasks_var[n], all(m in mem_choices) pdata_task[n][m]); 
   	  
	//span constraint for the data_tasks in the range of the data_tasks_var
	forall(t in Tasks)
		e:span(data_tasks[t], all(n in nvars, d in data_requirements:d.task_id == t && n == d.var_id) data_tasks_var[n]);
	
	//task_new[i] starts in the start of the task[i] and ends in the end of data_task[i]
	forall(t in Tasks){
	  g:startOf(task_new[t]) == startOf(task[t]);
	  h:endOf(task_new[t]) == endOf(data_tasks[t]);
 	};
		
	//precedence constraints for each data_task and computational task
	forall(t in Tasks)
	  i:endBeforeStart(task[t], data_tasks[t]);

	j:f <= nProcs;
	
	//spm size constraints
	forall(t in Tasks){
		forall(spm in spm_proc, p in Procs : spm.proc == p ){
		k:presenceOf(ptask[t][p]) * spm_usage[t] <= spm.spm_size;
		}
	};		

	//add communication 
    forall(e in Edges) {
    	forall (p1 in Procs, p2 in Procs: p1 != p2) {
			l:endBeforeStart(task_new[snode[e]], task_new[tnode[e]], presenceOf(ptask[snode[e]][p1])*presenceOf(ptask[tnode[e]][p2])*com[e]);
 		}	
 		
};
	
}	
	
	
 