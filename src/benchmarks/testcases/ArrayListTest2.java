package benchmarks.testcases ;

import benchmarks.AtomicBlock ;
import benchmarks.instrumented.java15.util.ArrayList;
import benchmarks.instrumented.java15.util.Collections;
import benchmarks.instrumented.java15.util.List;

/**
 * Created by IntelliJ IDEA.
 * User: ksen
 * Date: Jun 7, 2007
 * Time: 11:34:35 AM
 * To change this template use File | Settings | File Templates.
 */
public class ArrayListTest2 extends Thread {
		List al1, al2 ;
		int c ;

		public ArrayListTest2(List al1, List al2, int c) {
			this.al1 = al1 ;
			this.al2 = al2 ;
			this.c = c ;			
		}

    public void run() {
        Integer o1 = new Integer(4);

        switch (c) {
            case 0:
								AtomicBlock.begin() ;
                al1.add(o1);
								AtomicBlock.end() ;
                break;

            case 1:
								AtomicBlock.begin() ;
                al1.toArray();
								AtomicBlock.end() ;
                break;

            case 2:
								AtomicBlock.begin() ;
                al1.clear();
								AtomicBlock.end() ;
                break;

            case 3:
								AtomicBlock.begin() ;
                al1.contains(o1);
								AtomicBlock.end() ;
                break;

            case 4:
								AtomicBlock.begin() ;
                al1.size();
								AtomicBlock.end() ;
                break;

            case 5:
								AtomicBlock.begin() ;
                al1.remove(o1);
								AtomicBlock.end() ;
                break;

            case 6:
								AtomicBlock.begin() ;
                al1.indexOf(o1);
								AtomicBlock.end() ;
                break;

            case 7:
								AtomicBlock.begin() ;
                al1.isEmpty();
								AtomicBlock.end() ;
                break;

            case 8:
								AtomicBlock.begin() ;
                al1.lastIndexOf(o1);
								AtomicBlock.end() ;
                break;

            case 9:
								AtomicBlock.begin() ;
                al1.addAll(al2);
								AtomicBlock.end() ;
                break;

						default:
								break ; 
        }
    }

    public static void main(String args[]) {
				ArrayListTest2 [] threads = new ArrayListTest2[19] ;
				int i ;

        List al1 = Collections.synchronizedList(new ArrayList());
        List al2 = Collections.synchronizedList(new ArrayList());

				al1.add(new Integer(0)) ;
				al1.add(new Integer(1)) ;

				al2.add(new Integer(1)) ;
				al2.add(new Integer(2)) ;
        
				for (i = 0; i < 9; i++) {
            threads[i] = new ArrayListTest2(al1, al2, i) ;
						threads[i].start() ;
        }
        for (i = 0 ; i < 10; i++) {
						threads[i + 9] = new ArrayListTest2(al2, al1, i) ;
						threads[i + 9].start() ;
        }

				for (i = 0 ; i < 19 ; i++) {
					try {
						threads[i].join() ;
					}
					catch(InterruptedException ie) {
					}
				}
    }
}
