package javato.activetesting;

import java.util.*;
import java.util.Map.Entry;

import javato.activetesting.activechecker.ActiveChecker;
import javato.activetesting.analysis.AnalysisImpl;
import javato.activetesting.common.Parameters;

/**
 * Copyright (c) 2007-2008,
 * Koushik Sen    <ksen@cs.berkeley.edu>
 * All rights reserved.
 * <p/>
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are
 * met:
 * <p/>
 * 1. Redistributions of source code must retain the above copyright
 * notice, this list of conditions and the following disclaimer.
 * <p/>
 * 2. Redistributions in binary form must reproduce the above copyright
 * notice, this list of conditions and the following disclaimer in the
 * documentation and/or other materials provided with the distribution.
 * <p/>
 * 3. The names of the contributors may not be used to endorse or promote
 * products derived from this software without specific prior written
 * permission.
 * <p/>
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS
 * IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED
 * TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A
 * PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNER
 * OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,
 * EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO,
 * PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR
 * PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF
 * LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
 * NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
 * SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */

/*
 * This class will be used to analyze a multithreading program
 * for detecting race conditions occurring during runtime.
 * This program's data race detection algorithm will be based
 * on the dynamic data race detector Eraser by checking every
 * shared memory location following the lock discipline and
 * using global variables for memory location and heap memory
 * locations as shared memory locations.
 */
public class LocksetAnalysis extends AnalysisImpl 
{
	public enum MemoryState {Virgin, Exclusive, Shared, SharedModified};

	/* Data per thread -- */
	/*
	 * Contains stacks for each thread that contains sequences of iids of 
	 * method enter executions. This will keep in tract of methods entered
	 * during multithreading and their code locations.
	 */
	public HashMap<Integer /*thread*/, LinkedList<Integer> /*seq of iids*/>  stacks = new HashMap<Integer, LinkedList<Integer>>();
	
	/*
	 * Represents L(t): Sequence of lock identifiers held by a current thread.
	 * Let L(t) be the set of locks held by the thread 't' during multithreading.
	 * Locks will be added and removed during multithreading and be used to check
	 * for data races.
	 */
	public HashMap<Integer /*thread*/, LinkedList<Integer> /*seq of locks*/> heldLocks = new HashMap<Integer, LinkedList<Integer>>();
	/* -- Data per thread */

	/* Data per memory -- */
	/*
	 * Represents C(v): Contains sets of candidate locks for each memory location. 
	 * For each memory location 'v', initialize C(v) to be the set of all candidate 
	 * locks.
	 */
	public HashMap<Long /*memory*/, HashSet<Integer/*set of locks*/>> candidates = new HashMap<Long, HashSet<Integer>>();
	
	/*
	 * Contains monitoring states of each memory location during multithreading. 
	 * During each read/write operation, change the memory states accordingly to 
	 * the lock discipline.
	 */
	public HashMap<Long /*memory*/, MemoryState /*state*/> state = new HashMap<Long, MemoryState>();
	
	/*
	 * Contains the thread that first accesses memory location. This variable 
	 * will be used to record the first thread that accesses the memory location 
	 * and be checked if a new thread is accessing the memory location.
	 */
	public HashMap<Long /*memory*/, Integer /*thread*/> firstThread = new HashMap<Long, Integer>();
	
	/*
	 * Contains code line locations of each read/write operation that accesses the 
	 * memory location. This will be used to record the read/write operations that 
	 * occur right before the data race detection.
	 */
	public HashMap<Long /*memory*/, Integer /*iid*/> lastAccessLoc = new HashMap<Long, Integer>();
	
	/*
	 * Contains the memory locations and code line locations of where the data races
	 * are detected during lockset analysis and when the target program is executed
	 * and running.
	 */
	public HashMap<Long /*memory*/, List<String> /*iid*/> raceDetections = new HashMap<Long, List<String>>();
	/* -- Data per memory */

	/*
	 * This function will execute before a target program starts. This function
	 * is used to intialize the data structure and read user inputs. For this 
	 * program, it is used to intialize the variables for data per thread and
	 * memory.
	 */
	public void initialize()
	{
		stacks = new HashMap<Integer, LinkedList<Integer>>();
		heldLocks = new HashMap<Integer, LinkedList<Integer>>();
		candidates = new HashMap<Long, HashSet<Integer>>();
		state = new HashMap<Long, MemoryState>();
		firstThread = new HashMap<Long, Integer>();
		lastAccessLoc = new HashMap<Long, Integer>();
		raceDetections = new HashMap<Long, List<String>>();
	}

	/*
	 * This function will execute before a target method is called.
	 * This functions adds the iid of a method entered during 
	 * multithreading when the target program executes.
	 */
	public void methodEnterBefore(Integer iid, Integer thread, String method)
	{
		synchronized(stacks)
		{
			// Get the stack sequence of iids from the current thread.
			LinkedList<Integer> st = stacks.get(thread);

			// Check if there is a stack for the current thread.
			if(st == null)
            {
				/*
				 * Add a new empy stack to the current thread if
				 * the thread doesn't already have a stack.
				 */
				st = new LinkedList<Integer>();
				stacks.put(thread, st);
			}

			/*
			 * Pushes the iid into the stack for this thread which 
			 * represents the code location of a method called and
			 * entered durign multithreading.
			 */
			st.addFirst(iid);
		}
	}

	/*
	 * This function will execute before a target method is called.
	 * This functions removes the iid of a method exited during 
	 * multithreading when the target program executes.
	 */
	public void methodExitAfter(Integer iid, Integer thread, String method)
	{
		synchronized(stacks)
		{
			// Get the stack sequence of iids from the current thread.
			LinkedList<Integer> st = stacks.get(thread);
			
			// Pops the top-most iid from the stack.
			st.removeFirst();
		}
	}

	/*
	 * This function prints the stack trace of the current thread when 
	 * called. This function is executed when a data race is detected 
	 * during multithreading and prints out the given thread's stack
	 * trace.
	 */
	private void printStackTrace(Integer thread, Integer iid)
	{
		// Used to contain the stack of the given thread.
		LinkedList<Integer> st;

		// Start of printing the stack trace of the current thread.
		System.out.println("Stack trace of thread:" + thread);
		System.out.println("\tThread - " + javato.activetesting.analysis.Observer.getIidToLine(iid));

		synchronized(stacks)
		{
			// Get the stack sequence of iids from the current thread.
			st = stacks.get(thread);
			
			// Check if the stack isn't empty first.
			if (st != null)
            {
				// Iterate through the sequence of iids in the stack of the current thread.
				for (Iterator<Integer> itr = st.iterator(); itr.hasNext();)
				{
					// Print each code line location of each method entered in the current thread.
					System.out.println("\t" + javato.activetesting.analysis.Observer.getIidToLine(itr.next()));
				}
			}
		}
	}

	/*
	 * The function will execute before a synchronized block or a
	 * synchronized method call. This function is executed when a
	 * lock is acquired from the current thread and adds the lock
	 * to the set of locks acquired for the current thread during
	 * multithreading.
	 */
	public void lockBefore(Integer iid, Integer thread, Integer lock, Object actualLock)
	{
		synchronized(heldLocks)
		{
			// Check if there is a lock set for the current thread.
			if(!heldLocks.containsKey(thread))
			{
				/*
				 * Add a new empy set of locks to the current 
				 * thread if the thread doesn't already have a 
				 * set of locks.
				 */
				LinkedList<Integer> locks = new LinkedList<Integer>();
				heldLocks.put(thread, locks);
			}
			
			/*
			 * Check if the current thread already contains the current lock.
			 * This is to handle recursive locking, or when the same thread
			 * acquires the same lock multiple times without releasing it.
			 */
            if(!heldLocks.get(thread).contains(lock))
            {
            	/*
            	 * If the current thread doesn't already 
            	 * contain the current lock, then add the 
            	 * lock to the set of locks of the current 
            	 * thread.
            	 */
                heldLocks.get(thread).add(lock);
            }
		}
	}

	/*
	 * The function will execute after entering a synchronized 
	 * block or a synchronized method. 
	 */
	public void lockAfter(Integer iid, Integer thread, Integer lock, Object actualLock)
	{

	}

	/*
	 * The function will execute after an existing synchronized 
	 * block or a synchronized method. This function is executed 
	 * when a lock is released from the current thread and removes 
	 * the lock from the set of locks of current thread during
	 * multithreading. This method is assumed to be executed only
	 * after lockBefore(iid, thread, lock).
	 */
	public void unlockAfter(Integer iid, Integer thread, Integer lock)
	{
		synchronized(heldLocks)
		{
			// Check if there is a lock set for the current thread.
			if(!heldLocks.containsKey(thread))
			{
				/*
				 * Add a new empy set of locks to the current 
				 * thread if the thread doesn't already have a 
				 * set of locks.
				 */
				LinkedList<Integer> locks = new LinkedList<Integer>();
				heldLocks.put(thread, locks);
			}
			
			/*
			 * Check if the current thread already contains the current lock.
			 * This is to handle recursive locking, or when the same thread
			 * releases the same lock multiple times.
			 */
            if(heldLocks.get(thread).contains(lock))
            {
            	/*
            	 * If the current thread already contains
            	 * the current lock, then remove the lock
            	 * from the set of locks from the current
            	 * thread.
            	 */
                heldLocks.get(thread).remove(lock);
            }
		}
	}

	/*
	 * The function will execute before a new thread is starting. 
	 */
	public void startBefore(Integer iid, Integer parent, Integer child) 
	{
		
	}

	/*
	 * The function will execute after a thread awakens from a waiting.
	 */
	public void waitAfter(Integer iid, Integer thread, Integer lock) 
	{
		
	}

	/*
	 * The function will execute before notify(). 
	 */
	public void notifyBefore(Integer iid, Integer thread, Integer lock) 
	{
		
	}

	/*
	 * The function will execute before notifyAll(). 
	 */
	public void notifyAllBefore(Integer iid, Integer thread, Integer lock) 
	{
		
	}

	/*
	 * The function will execute after joining with a child thread.
	 */
	public void joinAfter(Integer iid, Integer parent, Integer child) 
	{
		
	}

    /*
     * This function will execute before every read operation.
     * This function makes memory state changes to a given memory
     * location depending on the lock discipline and checks for
     * data race detections depending on the intersection between
     * the current memory location's candidate lockset C(v) and the 
     * current thread's lockset L(t).
     * 
     * Memory State Changes for Read Operations:
     * 
     * 1) Virgin - If the current memory state is Virgin, then no
     * changes are made to the memory locations lockset and current
     * memory state.
     * 
     * 2) Exclusive - If the current memory state is Exclusive, then
     * if it is the first thread that accessed the memory location,
     * then the memory state isn't changed. Else, if it is a new thread
     * that accesses the memory location, then its memory state is changed
     * to Shared-Modified.
     * 
     * 3) Shared - If the current memory state is Shared, then the
     * memory state will remain as Shared.
     * 
     * 4) Shared-Modified - If the current memory state is Shared, then 
     * the memory state will remain as Shared-Modifed and check for data 
     * race detections.
     */
	public void readBefore(Integer iid, Integer thread, Long memory, boolean isVolatile)
	{
		// Check if the memory location's memory state is recorded already.
		if(!state.containsKey(memory))
		{
			/*
			 * If the state isn't already recorded for the memory location,
			 * intialize the memory location as memory state Virgin.
			 */
			state.put(memory, MemoryState.Virgin);
		}

		// Get the current memory state of the current memory location.
		MemoryState currentState = state.get(memory);

		// Make memory state changes for an Exclusive state.
		if(currentState == MemoryState.Exclusive)
		{
			/*
			 * Check if the a new thread is accessing the
			 * memory location different from the thread
			 * that first accessed the memory location.
			 */
			if(firstThread.get(memory) != thread)
			{
				/*
				 * If a new thread is accessing the memory 
				 * location change the memory state of the 
				 * current memory location to Shared and 
				 * intersect the candidate lockset C(v) and 
				 * the lockset of the current thread L(t).
				 */
                state.put(memory, MemoryState.Shared);
                intersectLocks(memory, thread);
			}
		}

		// Make memory state changes for a Shared state.
		else if(currentState == MemoryState.Shared)
		{
			/*
			 * Intersect the locksets, which are the candidate 
			 * lockset of the memory location C(v) and the lockset 
			 * of the current thread L(t).
			 */
			intersectLocks(memory, thread);
		}

		// Make memory state changes for a Shared-Modified state.
		else if(currentState == MemoryState.SharedModified)
		{
			/*
			 * Intersect the locksets, which are the candidate 
			 * lockset of the memory location C(v) and the lockset 
			 * of the current thread L(t).
			 */
			intersectLocks(memory, thread);

			/*
			 * Check if the memory location is volatile and the
			 * current candidate lockset of the memory location
			 * C(v) is empty after intersecting locksets.
			 */
			if(!isVolatile && candidates.get(memory).isEmpty())
            {
				/*
				 * If so, print the stack trace of the current thread
				 * and the code line location that has last accessed
				 * the memory location and record the memory location
				 * and its code line location of where the data race
				 * occurs.
				 */
                printStackTrace(thread, iid);
				System.out.println("Last accessed memory location: " + javato.activetesting.analysis.Observer.getIidToLine(lastAccessLoc.get(memory)));
				if(!raceDetections.containsKey(memory))
					raceDetections.put(memory,new ArrayList<String>());
				raceDetections.get(memory).add(javato.activetesting.analysis.Observer.getIidToLine(iid));
            }
		}

		/*
		 * Record each read/write operation on the memory location to
		 * get the iid of the last access to the memory location before
		 * the data race occurs.
		 */
		lastAccessLoc.put(memory, iid);
	}

	/*
     * This function will execute after every read operation.
     */
	public void readAfter(Integer iid, Integer thread, Long memory, boolean isVolatile)
	{
		
	}

	/*
     * This function will execute before every write operation.
     * This function makes memory state changes to a given memory
     * location depending on the lock discipline and checks for
     * data race detections depending on the intersection between
     * the current memory location's candidate lockset C(v) and the 
     * current thread's lockset L(t).
     * 
     * Memory State Changes for Write Operations:
     * 
     * 1) Virgin - If the current memory state is Virgin, then the
     * memory state of the memory location is changed to Exclusive
     * and the thread that first accessed the memory location is
     * recorded..
     * 
     * 2) Exclusive - If the current memory state is Exclusive, then
     * if it is the first thread that accessed the memory location,
     * then the memory state isn't changed. Else, if it is a new thread
     * that accesses the memory location, then its memory state is changed
     * to Shared-Modified.
     * 
     * 3) Shared - If the current memory state is Shared, then the
     * memory location's memory state is changed to Shared-Modified.
     * 
     * 4) Shared-Modified - If the current memory state is Shared, then 
     * the memory state will remain as Shared-Modified and check for data 
     * race detections.
     */
	public void writeBefore(Integer iid, Integer thread, Long memory, boolean isVolatile)
	{
		/*
		 * Check if the memory location's memory 
		 * state is recorded already.
		 */
		if(!state.containsKey(memory))
		{
			/*
			 * If the state isn't already recorded for the memory location,
			 * intialize the memory location as memory state Virgin.
			 */
			state.put(memory, MemoryState.Virgin);
		}
		
		/*
		 * Get the current memory state of the 
		 * current memory location.
		 */
		MemoryState currentState = state.get(memory);

		// Make memory state changes for a Virgin state.
		if(currentState == MemoryState.Virgin)
		{
			/*
			 * Change the memory state of the current
			 * memory location to Exclusive and record
			 * the first thread that accesses the memory
			 * location.
			 */
            state.put(memory, MemoryState.Exclusive);
            firstThread.put(memory, thread);
		}

		// Make memory state changes for an Exclusive state.
		else if(currentState == MemoryState.Exclusive)
		{
			/*
			 * Check if the a new thread is accessing the
			 * memory location different from the thread
			 * that first accessed the memory location.
			 */
			if(firstThread.get(memory) != thread)
			{
				/*
				 * If a new thread is accessing the memory 
				 * location change the memory state of the 
				 * current memory location to Shared-Modified 
				 * and intersect the candidate lockset C(v) and 
				 * the lockset of the current thread L(t).
				 */
                state.put(memory, MemoryState.SharedModified); 
                intersectLocks(memory, thread);
                
                if(!isVolatile && candidates.get(memory).isEmpty())
                {
                	/*
    				 * If so, print the stack trace of the current thread
    				 * and the code line location that has last accessed
    				 * the memory location and record the memory location
    				 * and its code line location of where the data race
    				 * occurs.
    				 */
                    printStackTrace(thread, iid);
                    System.out.println("Last accessed memory location: " + javato.activetesting.analysis.Observer.getIidToLine(lastAccessLoc.get(memory)));
					
					if(!raceDetections.containsKey(memory))
						raceDetections.put(memory,new ArrayList<String>());
					raceDetections.get(memory).add(javato.activetesting.analysis.Observer.getIidToLine(iid));
                }
			}
		}

		// Make memory state changes for an Shared state.
		else if(currentState == MemoryState.Shared)
		{
			/*
			 * Change the memory state of the current memory location 
			 * to Shared-Modified and intersect the candidate lockset 
			 * C(v) and the lockset of the current thread L(t).
			 */
            state.put(memory, MemoryState.SharedModified);
			intersectLocks(memory, thread);
			if(!isVolatile && candidates.get(memory).isEmpty())
            {
				/*
					* If so, print the stack trace of the current thread
					* and the code line location that has last accessed
					* the memory location and record the memory location
					* and its code line location of where the data race
					* occurs.
					*/
				printStackTrace(thread, iid);
				System.out.println("Last accessed memory location: " + javato.activetesting.analysis.Observer.getIidToLine(lastAccessLoc.get(memory)));
				
				if(!raceDetections.containsKey(memory))
					raceDetections.put(memory,new ArrayList<String>());
				raceDetections.get(memory).add(javato.activetesting.analysis.Observer.getIidToLine(iid));
            }
		}

		// Make memory state changes for an Shared-Modified state.
		else if(currentState == MemoryState.SharedModified)
		{
			/*
			 * Intersect the locksets, which are the candidate 
			 * lockset of the memory location C(v) and the lockset 
			 * of the current thread L(t).
			 */
			intersectLocks(memory, thread);

			/*
			 * Check if the memory location is volatile and the
			 * current candidate lockset of the memory location
			 * C(v) is empty after intersecting locksets.
			 */
			if(!isVolatile && candidates.get(memory).isEmpty())
            {
				/*
				 * If so, print the stack trace of the current thread
				 * and the code line location that has last accessed
				 * the memory location and record the memory location
				 * and its code line location of where the data race
				 * occurs.
				 */
                printStackTrace(thread, iid);
                System.out.println("Last accessed memory location: " + javato.activetesting.analysis.Observer.getIidToLine(lastAccessLoc.get(memory)));
                if(!raceDetections.containsKey(memory))
					raceDetections.put(memory,new ArrayList<String>());
				raceDetections.get(memory).add(javato.activetesting.analysis.Observer.getIidToLine(iid));
            }
		}

		/*
		 * Record each read/write operation on the memory location to
		 * get the iid of the last access to the memory location before
		 * the data race occurs.
		 */
		lastAccessLoc.put(memory, iid);
	}

	/*
     * This function will execute after every write operation.
     */
	public void writeAfter(Integer iid, Integer thread, Long memory, boolean isVolatile)
	{

	}
	
	/*
	 * This function is used to update the candidate lockset of the memory 
	 * location C(v) by intersecting candidate locks of the current memory 
	 * location C(v) and the locks currently held by a given thread L(t) 
	 * and having C(v) equal the resulting intersection of locks.
	 */
	private void intersectLocks(Long memory, Integer thread)
	{
		/*
		 * Check if there is a candidate lockset provided for
		 * the memory location already. This in particular is
		 * considered the first update to the candidate lockset
		 * of the memory location C(v).
		 */
		if(!candidates.containsKey(memory))
		{
			/*
			 * If so, copy the locks held by the current thread L(t)
			 * onto the new candidate lockset C(v). This is because
			 * C(v) should initially contain all locks at the start
			 * of multithreading and having an intersection to the
			 * held locks of the current thread should just be the
			 * same locks held by the current thread.
			 */
			HashSet<Integer> lockset = new HashSet<Integer>();
			
			// Check if the HashMap contains the thread already.
			if(heldLocks.containsKey(thread))
			{
				for(int i = 0; i < heldLocks.get(thread).size(); i++)
				{
					lockset.add(heldLocks.get(thread).get(i));
				}
			}
			
			// Add a lockset to the thread is there isn't one added already.
			else
			{
				LinkedList<Integer> locks = new LinkedList<Integer>();
				heldLocks.put(thread, locks);
			}
			
			// Update the candidate lockset for the memory location.
			candidates.put(memory, lockset);
		}
		
		/*
		 * Else, if there is a candidate lockset provided for the 
		 * memory location, intersect the locks that are in both 
		 * C(v) of the current memory location and L(t) of the 
		 * current thread.
		 */
		else
		{
			// Check if the HashMap contains the thread already. If not, add a lockset to the thread.
			if(!heldLocks.containsKey(thread))
			{
				LinkedList<Integer> locks = new LinkedList<Integer>();
				heldLocks.put(thread, locks);
			}
			
			candidates.get(memory).retainAll(heldLocks.get(thread));
		}
	}

	/*
	 * This function will execute when the target program terminates.
	 * This function will analyze the monitored data and print out the 
	 * results. These results will contain the number of data race 
	 * detections and the memory and code locations of where the 
	 * data races occur.
	 */
	public void finish()
	{
		System.out.println("Lockset Analysis -");
		System.out.println("Total # of data race detections: " + raceDetections.size());
		
		// Identify the memory locations and code line locations of each data race.
		
		// Get each detection of a data race with its memory location and code line location.
		for (Entry<Long, List<String>> entry : raceDetections.entrySet())
		{
			/*
			 * Get the memory and code locations from the 
			 * HashMap's Key and Value.
			 */
			Long memory = entry.getKey();
			List<String> list = entry.getValue();

			for(String code : list) {
				System.out.println("Memory Location:\t\tCode Location:");

			
				// Print the data race's memory location and code line location.
				System.out.println(memory + "\t\t" + code);	
			}
			
		}
	}
}

