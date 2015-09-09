/*
 * created by Junyuan Zhang
 * Sept.9th.2015
 */
package lts;


public class TraceProduceOptions {
	private static int traceNumber = 5;
	private static int maxSimilarity = 100000;
	
	public static void setTraceNumber(int tn){
		traceNumber = tn;
	}
	
	public static int getTraceNumber(){
		return traceNumber;
	}
	
	public static void setMaxSimilarity(int ms){
		maxSimilarity = ms;
	}
	
	public static int getMaxSimilarity(){
		return maxSimilarity;
	}
	
}
