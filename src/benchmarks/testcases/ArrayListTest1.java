package benchmarks.testcases ;

import benchmarks.instrumented.java15.util.ArrayList;
import benchmarks.instrumented.java15.util.Collections;
import benchmarks.instrumented.java15.util.List;

/*
 * This class will be used for testing the lockset analysis program
 * for detecting data races during multithreading. 
 */
public class ArrayListTest1 extends Thread
{
    List al1;
    int c;

    public ArrayListTest1(List al1, int c)
    {
        this.al1 = al1;
        this.c = c;
    }

    public void run()
    {
        Integer o1 = new Integer(4);

        switch (c)
        {
            case 0:
                al1.add(o1);
                break;

            case 1:
                al1.toArray();
                break;

            case 2:
                al1.clear();
                break;

            case 3:
                al1.contains(o1);
                break;

            case 4:
                al1.size();
                break;

            case 5:
                al1.remove(o1);
                break;

            case 6:
                al1.iterator();
                break;

            case 7:
                al1.indexOf(o1);
                break;

            case 8:
                al1.isEmpty();
                break;

            case 9:
                al1.lastIndexOf(o1);
                break;

            default:
                break;
        }
    }

    public static void main(String args[])
    {
        ArrayListTest1 [] threads = new ArrayListTest1[10];
        int i;

        List al1 = new ArrayList();

        al1.add(new Integer(0));
        al1.add(new Integer(1));
        al1.add(new Integer(2));

        for (i = 0; i < 10; i++)
        {
            threads[i] = new ArrayListTest1(al1, i);
            threads[i].start();
        }

        for (i = 0 ; i < 10 ; i++)
        {
            try
            {
                threads[i].join();
            }

            catch(InterruptedException ie)
            {

            }
        }
    }
}
