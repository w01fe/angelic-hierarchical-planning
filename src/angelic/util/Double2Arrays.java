package angelic.util;

import java.util.*;

public class Double2Arrays {
    public static double [][] toDouble2Array(List l) {
	int n = l.size();
	int m = ((List)l.get(0)).size();
	double [][] ret = new double[n][m];
	int i = 0;
	for (Object o : l) {
	    List l2 = (List) o;
	    int j = 0;
	    for (Object o2 : l2) {
		ret[i][j++] = ((Number)o2).doubleValue();
	    }
	    i++;
	}
	return ret;
    }

    public static double get(double [][] arr, int i, int j) {return arr[i][j]; }
    public static void set(double [][] arr, int i, int j, double v) {arr[i][j] = v;}
}