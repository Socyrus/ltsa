//created by Junyuan Zhang
package lts;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.Stack;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import ui.HPWindow;

public class AsynTranslation {
	private String axioms = 
			"%*******************************\n"+
					"% --*** BACKGROUND THEORY ***---\n"+
					"%*******************************\n"+
					"\n"+
					"% --*** DOMAIN INDEPENDENT AXIOMS ***---\n"+
					"\n"+
					"% (EC1)\n"+
					"clipped(T1,F,T2,S) :- 	\n"+
					"		  	timepoint(T),\n"+
					"               		timepoint(T1),\n"+
					"                    	timepoint(T2),	\n"+
					"                    	fluent(F),\n"+
					"                    	event(E), \n"+
					"		    	scenario(S),\n"+
					"                    	happens(E,T,S),\n"+
					"                    	T1<=T,\n"+
					"                    	T<T2,\n"+
					"                    	terminates(E,F).\n"+
					"% (EC2)\n"+
					"declipped(T1,F,T2,S) :- 	\n"+
					"			timepoint(T),\n"+
					"                   	timepoint(T1),\n"+
					"                    	timepoint(T2),	\n"+
					"                    	fluent(F),\n"+
					"                    	event(E), \n"+
					"		    	scenario(S),\n"+
					"                   	happens(E,T,S),\n"+
					"                    	T1<=T,\n"+
					"                    	T<T2,\n"+
					"                    	initiates(E,F).\n"+
					"\n"+
					"% (EC3)\n"+
					"stopped_in(T1,F,T2,S) :- \n"+
					"			timepoint(T),\n"+
					"                       	timepoint(T1),\n"+
					"                       	timepoint(T2),\n"+
					"                       	fluent(F),\n"+
					"                       	event(E),\n"+
					"			scenario(S),\n"+
					"                       	happens(E,T,S),\n"+
					"                       	T1<T,\n"+
					"                       	T<T2,\n"+
					"                       	terminates(E,F).\n"+
					"\n"+
					"% (EC4)\n"+
					"started_in(T1,F,T2,S) :- \n"+
					"			timepoint(T),\n"+
					"                       	timepoint(T1),\n"+
					"                       	timepoint(T2),\n"+
					"                       	fluent(F),\n"+
					"                       	event(E),\n"+
					"			scenario(S),\n"+
					"                       	happens(E,T,S),\n"+
					"                       	T1<T,\n"+
					"                       	T<T2,\n"+
					"                       	initiates(E,F).\n"+
					"\n"+
					"% (EC5)\n"+
					"holds_at(F,T2,S) :- 	\n"+
					"				timepoint(T1),\n"+
					"                      	timepoint(T2),\n"+
					"                      	fluent(F),\n"+
					"                      	event(E),\n"+
					"				scenario(S),\n"+
					"                      	happens(E,T1,S),\n"+
					"                      	initiates(E,F),\n"+
					"                      	T1<T2,             \n"+
					"                      	not stopped_in(T1,F,T2,S).\n"+
					"% (EC7)\n"+
					"holds_at(F,T2,S) :- 	\n"+
					"				timepoint(T1),\n"+
					"                  	timepoint(T2),\n"+
					"                  	fluent(F), scenario(S),\n"+
					"                  	holds_at(F,T1,S),\n"+
					"                  	T1<T2,\n"+
					"                  	not clipped(T1,F,T2,S).\n"+
					"\n"+
					"% (EC8)\n"+
					"holds_at(F,0,S):-	 \n"+
					"			fluent(F), \n"+
					"			scenario(S), \n"+
					"			initially(F,S).\n"+
					"% (EC9)\n"+
					"happens(A,P,S):-  	\n"+
					"			event(A),\n"+
					"			scenario(S), \n"+
					"			timepoint(P),				\n"+
					"		 	attempt(A,P,S), \n"+
					"			not impossible(A,P,S).\n"+
					"\n"+
					"% (EC10)\n"+
					"happens(A,P,S):-  	\n"+
					"			event(A),\n"+
					"			scenario(S), \n"+
					"			timepoint(P),				\n"+
					"			triggered(A,P,S).\n"+
					" \n"+
					"% (EC11)\n"+
					"impossible(A2,P,S):-\n"+
					"			event(A2),\n"+
					"			scenario(S), \n"+
					"			timepoint(P),\n"+
					"			event(A1),	\n"+
					"			A1 != A2,\n"+
					"			triggered(A1,P,S).\n"+
					"\n"+
					"% --*** CONSTRAINTS  ***--- \n"+
					"\n"+
					":- timepoint(T),            \n"+
					"	event(A1),event(A2), \n"+
					"	A1 != A2, scenario(S), \n"+
					"	happens(A1,T,S),\n"+
					"	happens(A2,T,S).\n"+
					"\n"+
					":- timepoint(T),            \n"+
					"	event(A1), \n"+
					"	triggered(A1,T,S),\n"+
					"	impossible(A1,T,S).\n"+
					"\n";
	
	private String modes = 
			"% ---*** MODES ***---\n\n" + 
			"modeh(impossible(\"#sys\",\"+timepoint\",\"+scenario\")).\n"+
			"modeh(impossible(\"#sys\",\"+timepoint\",\"+scenario\")).\n"+
			"\n"+
			"\n"+
			"modeb(holds_at(\"#fluent\",\"+timepoint\",\"+scenario\")).\n"+
			"modeb(not holds_at(\"#fluent\",\"+timepoint\",\"+scenario\")).\n";



	
	private boolean error = false;
	HashSet<String> fluentList = new HashSet<String>();
	HashMap<String, HashSet<String>> initiates = new HashMap<String, HashSet<String>>();
	HashMap<String, HashSet<String>> terminates = new HashMap<String, HashSet<String>>();
	HashSet<String> initialValue = new HashSet<String>();
	HashSet<String> eventList = new HashSet<String>();
	HashMap<String, HashSet<String>> setList = new HashMap<String, HashSet<String>>();
	HashSet<String> systemList = new HashSet<String>();
	LinkedList<String> constraintLeft = new LinkedList<String>();
	LinkedList<String> constraintRight = new LinkedList<String>();
	LinkedList<String> goalLeft = new LinkedList<String>();
	LinkedList<String> goalRight = new LinkedList<String>();
	
	private boolean pair(char a, char b){
		if (a == '(' && b == ')') return true;
		if (a == '[' && b == ']') return true;
		if (a == '{' && b == '}') return true;
		if (a == '<' && b == '>') return true;
		return false;
	}
	
	private boolean complete(String line, HPWindow window){
		if (line.endsWith(","))
			return false;
		
		Stack<Character> stack = new Stack<Character>();
		int length = line.length();
		boolean flag = false;
		for (int i=0;i<length;i++){
			if (line.charAt(i) == '{' || 
				line.charAt(i) == '(' ||
				line.charAt(i) == '[' ||
				line.charAt(i) == '<'){
				stack.add(line.charAt(i));
				flag = true;
			}
			else if (line.charAt(i) == '}' || 
					line.charAt(i) == ')' ||
					line.charAt(i) == ']' ||
					line.charAt(i) == '>'){
					if (i >0 && line.charAt(i-1) == '-') continue;
					if (stack.isEmpty()){
						window.outln("wrong brackets");
						window.outln(line);
						error = true;
						return false;
					}
					
					char tmp = stack.pop();
					if (!pair(tmp,line.charAt(i))){
						window.outln("wrong brackets");
						window.outln(line);
						error = true;
						return false;
					}	
			}
		}	
		return (stack.isEmpty() && flag);
	}
	
	private void newFluent(String line){
		String[] splits = line.split("=");
		
		String fluentName = "";
		Pattern p = Pattern.compile("\\w+");
		Matcher m = p.matcher(splits[0]);
		while (m.find()){
			String tmp = splits[0].substring(m.start(), m.end());
			if (!tmp.equals("fluent")){
				fluentName = tmp;
				break;
			}
		}
		
		fluentList.add(fluentName);
		initiates.put(fluentName, new HashSet<String>());
		terminates.put(fluentName, new HashSet<String>());
		
		boolean inBracket = false;
		int place = 0;
		for (int i=0;i<splits[1].length();i++){
			if (splits[1].charAt(i) == '{'){
				inBracket = true;
				continue;
			}
			
			if (splits[1].charAt(i) == '}'){
				inBracket = false;
				continue;
			}
			
			if (inBracket) continue;
			
			if (splits[1].charAt(i)==','){
				place = i;
				break;
			}
		}
		
		p = Pattern.compile("\\w+");
		m = p.matcher(splits[1]);
		while (m.find()){
			if (m.start()<place){
				initiates.get(fluentName).add(splits[1].substring(m.start(), m.end()));
			}else{
				if (splits[1].substring(m.start(), m.end()).equals("initially")){
					initialValue.add(fluentName);
					break;
				}
				terminates.get(fluentName).add(splits[1].substring(m.start(), m.end()));
			}
		}
		eventList.addAll(initiates.get(fluentName));
		eventList.addAll(terminates.get(fluentName));
	}
	
	private void newSet(String line){
		String[] splits = line.split("=");
		String setName = "";
		boolean isSystem = false;
		Pattern p = Pattern.compile("\\w+");
		Matcher m = p.matcher(splits[0]);
		while (m.find()){
			String tmp = splits[0].substring(m.start(), m.end());
			if (tmp.equals("set")) continue;
			if (tmp.equals("system")) {isSystem = true;continue;}
			setName = tmp;
			break;
		}
		
		setList.put(setName, new HashSet<String>());
		m = p.matcher(splits[1]);
		while (m.find()){
			String tmp = splits[1].substring(m.start(), m.end());
			if (setList.containsKey(tmp))
				setList.get(setName).addAll(setList.get(tmp));
			else
				setList.get(setName).add(tmp);
		}
		
		if (isSystem) systemList.addAll(setList.get(setName));
	}
	
	private String strip(String str){
		return str.replace("(", "").replace(")", "").replace(" ", "");
	}
	
	private void newConstraint(String line){
		line = line.split("=")[1];
		String tmp = "";
		int length = line.length();
		boolean flag = false;
		int bracketCount =0 ;
		for (int i=0;i<length;i++){
			if (!flag){
				tmp = tmp + line.charAt(i);
				if (tmp.endsWith("[]")){
					bracketCount = 0;
					tmp = "";
					flag = true;
				}
			}
			else{
				tmp = tmp + line.charAt(i);
				if (line.charAt(i) == '(')
					bracketCount+=1;
				else if (line.charAt(i) == ')'){
					bracketCount-=1;
					if (bracketCount == 0){
						String[] splits = tmp.split("->");
						constraintLeft.addLast(strip(splits[0]));
						splits[1] = splits[1].substring(splits[1].indexOf('X')+1);
						constraintRight.addLast(strip(splits[1]));
						
						tmp = "";
					}
				}
			}
		}
	}
	
	private void newGoal(String line) {
		line = line.split("=")[1].replace("[]", "");
		
		String[] splits = line.split("->");
		
		String left = strip(splits[0]);
		splits[1] = strip(splits[1]);
		String right = splits[1].substring(splits[1].indexOf('X')+1);
		
		
		goalLeft.addLast(left);
		goalRight.addLast(right);
		
	}
	
	private String lowerFirstLetter(String str){
		if (str==null || str.equals(""))
			return str;
		for (int i=0;i<str.length();i++){
			if ((str.charAt(i) >='A' && str.charAt(i)<='Z') || (str.charAt(i) >= 'a' && str.charAt(i)<='z')){
				if (i==str.length()-1) return str.toLowerCase();
				else return str.substring(0, i+1).toLowerCase()+str.substring(i+1);
			}
		}
		return str;
	}
	
	private void printSet(BufferedWriter writer, String setName, HashSet<String> set) throws IOException{
		writer.write(setName+"(");
		boolean first = true;
		for (String item:set){
			if (!first)
				writer.write(";");
			first = false;
			writer.write(lowerFirstLetter(item));
		}
		writer.write(").\n");
	}
	
	private void printTypes(BufferedWriter writer) throws IOException{
		writer.write("% --*** TYPES ***---\n");
		
		int nTimepoint = 12;
		writer.write("timepoint(0.."+nTimepoint+").\n");
		
		printSet(writer,"evnet",eventList);
		printSet(writer,"fluent",fluentList);
		printSet(writer,"sys",systemList);
		
		writer.write("\n\n");
	}
	
	private void printInitsNTerms(BufferedWriter writer) throws IOException{
		writer.write(" --*** DOMAIN POSTCONDITIONS ***--\n\n");
		
		for (String fluent:initiates.keySet()){
			for (String action:initiates.get(fluent)){
				writer.write("initiates(" + lowerFirstLetter(action) + "," + lowerFirstLetter(fluent) + ").\n");
			}
		}
		
		for (String fluent:terminates.keySet()){
			for (String action:terminates.get(fluent)){
				writer.write("terminates(" + lowerFirstLetter(action) + "," + lowerFirstLetter(fluent) + ").\n");
			}
		}
		
		writer.write("\n\n");
	}
	
	private void printHoldsAt(BufferedWriter writer,String con, boolean isLast, boolean reverse,boolean next) throws IOException{
		String result = "";
		con = lowerFirstLetter(con);
		if (con.startsWith("!")){
			if (reverse)  result = "\t\tholds_at("+con.replace("!", "")+",T,S)";
			else	result = "\t\tnot holds_at("+con.replace("!", "")+",T,S)";
		}
		else{
			if (reverse) result = "\t\tnot holds_at("+con+",T,S)";
			else	result = "\t\tholds_at("+con+",T,S)";
		}
		
		if (next)
			result = result.replace(",T,S)",",T+1,S)");
		
		if (isLast) result = result+".\n";
		else result = result + ",\n";
		writer.write(result);
	}
	
	private void printConstraints(BufferedWriter writer) throws IOException{
		writer.write("% --*** DOMAIN PRECONDITIONS ***---\n");
		while(!constraintLeft.isEmpty()){
			String left = constraintLeft.pop();
			String right = constraintRight.pop();
			left = strip(left);
			right = strip(right);
			
			String[] lefts = left.split("\\|\\|");
			
			for (int i=0;i<lefts.length;i++){	
					String[] rights = right.split("&&");
					for (int j=0; j<rights.length;j++){
						if (rights[j].startsWith("!"))
							writer.write("impossible("+rights[j].replace("!", "")+",T,S):-\n");	
						else
							writer.write("happens("+rights[j]+",T,S):-\n");
						writer.write("\t\tscenario(S),\n");
						writer.write("\t\ttimepoint(T),\n");
						String tmp[] = lefts[i].split("&&");
						for (int k=0;k<tmp.length;k++){
							printHoldsAt(writer,tmp[k],k == tmp.length-1,false,false);
						}
					}
			}
		}
	}
	
	private void printInitialValue(BufferedWriter writer) throws IOException{
		
		writer.write("% --*** INITIAL STATE ***---\n\n");
		for (String fluent:initialValue){
			writer.write("initially("+lowerFirstLetter(fluent)+"):-\n");
			writer.write("\tscenario(S).\n");
		}
	}
	
	private void printGoals(BufferedWriter writer) throws IOException{
		writer.write("% --*** GOALS ***----\n\n");
		while (!goalLeft.isEmpty()){
			String left = goalLeft.pop();
			String right = goalRight.pop();
			String[] lefts = left.split("\\|\\|");
			
			for (int i=0;i<lefts.length;i++){
				String[] condition = lefts[i].split("&&");
				String[] rights = right.split("\\|\\|");
				
				writer.write(":-scenario(S), timepoint(T),\n");
				for (int j=0;j<condition.length;j++)
					printHoldsAt(writer,condition[j],false,false,false);
				
				for (int j=0;j<rights.length;j++)
					printHoldsAt(writer,rights[j],j==rights.length-1,true,true);
			}
		}
	}
	
	public boolean translate(String fromDirectory, String toDirectory, HPWindow window){
		BufferedReader reader = null;
		try {
			 reader = new BufferedReader(new FileReader(new File(fromDirectory)));
		} catch (FileNotFoundException e) {
			window.outln("File not found");
			e.printStackTrace();
			return false;
		}
		
		String line = null;
		String tmp = "";
		boolean inComment = false;
		
		try{
			while ((line=reader.readLine())!=null){
				if (line.trim().startsWith("//")) continue;
				
				if (line.trim().startsWith("/*")){
					if (!line.trim().endsWith("*/"))
						inComment = true;
					continue;
				}
				
				if (inComment){
					if (line.trim().endsWith("*/"))
						inComment = false;
					continue;
				}
				
				tmp = tmp + line.trim();
				
				if (complete(tmp,window)){
					if 	(tmp.startsWith("fluent"))
						newFluent(tmp);
					else if (tmp.startsWith("set"))
						newSet(tmp);
					else if (tmp.startsWith("constraint"))
						newConstraint(tmp);
					else if (tmp.startsWith("assert"))
						newGoal(tmp);
					
					tmp = "";
				}
				if (error) {reader.close();return false;}

			}
			reader.close();
		}catch (IOException e){
			window.outln("IO Exception");
			e.printStackTrace();
			return false;
		}
		
		System.out.println("Fluents:");
		for (String fluent:fluentList){
			System.out.print(" "+fluent);
			System.out.println();
		}
		
		System.out.println("initiates:");
		for (String fluent:fluentList){
			System.out.print(fluent+" :");
			for (String init:initiates.get(fluent)){
				System.out.print(" "+init);
			}
			System.out.println();
		}
		
		System.out.println("terminates:");
		for (String fluent:fluentList){
			System.out.print(fluent+" :");
			for (String term:terminates.get(fluent)){
				System.out.print(" "+term);
			}
			System.out.println();
		}
		
		System.out.println("sets:");
		for (String setName : setList.keySet()){
			System.out.print(setName+" :");
			for (String item:setList.get(setName)){
				System.out.print(" "+item);
			}
			System.out.println();
		}
		
		System.out.println("constraintLefts:");
		for (String left: constraintLeft){
			System.out.println(left);
		}
		
		System.out.println("constraintRights:");
		for (String right: constraintRight){
			System.out.println(right);
		}
		
		System.out.println("goalLeft:");
		for (String left: goalLeft){
			System.out.println(left);
		}
		
		System.out.println("goalRight:");
		for (String right: goalRight){
			System.out.println(right);
		}
		
		BufferedWriter writer = null;
		
		try {
			writer = new BufferedWriter(new FileWriter(toDirectory));
			
			writer.write(axioms);
			
			printTypes(writer);
			
			printInitsNTerms(writer);
			
			printConstraints(writer);
			
			printInitialValue(writer);
			
			printGoals(writer);
			
			writer.write(modes);
			
			writer.close();
			
		} catch (IOException e) {
			window.outln("IO Exception caught while writing file");
			e.printStackTrace();
			return false;
		}
		
		return true;
	}

	
}
