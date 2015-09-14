//Created by Junyuan Zhang
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
import java.util.Map;
import java.util.Stack;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import ui.HPWindow;

public class SynTranslation {
	private String axiom = 
					"\n"+
					"% *******************************\n"+
					"% --*** BACKGROUND THEORY ***---\n"+
					"% *******************************\n"+
					"\n"+
					"% --*** DOMAIN INDEPENDENT AXIOMS ***---\n"+
					"\n"+
					"% (EC1)\n"+
					"clipped(T1,F,T2,S) :-\n"+
					"		  	timepoint(T),\n"+
					"               		timepoint(T1),\n"+
					"                    	timepoint(T2),\n"+
					"                    	fluent(F),\n"+
					"                    	event(E),\n"+
					"		    	scenario(S),\n"+
					"                    	happens(E,T,S),\n"+
					"                    	T1<=T,\n"+
					"                    	T<T2,\n"+
					"                    	terminates(E,F).\n"+
					"% (EC2)\n"+
					"declipped(T1,F,T2,S) :-\n"+
					"			timepoint(T),\n"+
					"                   	timepoint(T1),\n"+
					"                    	timepoint(T2),\n"+
					"                    	fluent(F),\n"+
					"                    	event(E),\n"+
					"		    	scenario(S),\n"+
					"                   	happens(E,T,S),\n"+
					"                    	T1<=T,\n"+
					"                    	T<T2,\n"+
					"                    	initiates(E,F).\n"+
					"\n"+
					"% (EC3)\n"+
					"stopped_in(T1,F,T2,S) :-\n"+
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
					"started_in(T1,F,T2,S) :-\n"+
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
					"holds_at(F,T2,S) :-\n"+
					"				timepoint(T1),\n"+
					"                      	timepoint(T2),\n"+
					"                      	fluent(F),\n"+
					"                      	event(E),\n"+
					"				scenario(S),\n"+
					"                      	happens(E,T1,S),\n"+
					"                      	initiates(E,F),\n"+
					"                      	T1<T2,\n"+
					"                      	not stopped_in(T1,F,T2,S).\n"+
					"% (EC7)\n"+
					"holds_at(F,T2,S) :-\n"+
					"				timepoint(T1),\n"+
					"                  	timepoint(T2),\n"+
					"                  	fluent(F), scenario(S),\n"+
					"                  	holds_at(F,T1,S),\n"+
					"                  	T1<T2,\n"+
					"                  	not clipped(T1,F,T2,S).\n"+
					"\n"+
					"% (EC8)\n"+
					"holds_at(F,0,S):-\n"+
					"			fluent(F),\n"+
					"			scenario(S),\n"+
					"			initially(F,S).\n"+
					"% (EC9)\n"+
					"happens(A,P,S):-\n"+
					"			event(A),\n"+
					"			scenario(S),\n"+
					"			timepoint(P),\n"+
					"		 	executed(A,P,S),\n"+
					"			not impossible(A,P,S).\n"+
					"\n"+
					"% (EC10)\n"+
					"holds_at_tick(F,P,S):-\n"+
					"			scenario(S),\n"+
					"			fluent(F),\n"+
					"			timepoint(P),\n"+
					"         		happens(tick,P,S),\n"+
					"			holds_at(F,P,S).\n"+
					"\n"+
					"% (EC11)\n"+
					"not_holds_at_tick(F,P,S):-\n"+
					"			scenario(S),\n"+
					"			fluent(F),\n"+
					"			timepoint(P),\n"+
					"        		happens(tick,P,S),\n"+
					"			not holds_at(F,P,S).\n"+
					"\n"+
					"% (EC12)\n"+
					"holds_at_prev_tick(F,P,S):-\n"+
					"         		scenario(S),\n"+
					"			fluent(F),\n"+
					"			timepoint(P),\n"+
					"			timepoint(P0),\n"+
					"			P0<P,\n"+
					"         		happens(tick,P0,S),\n"+
					"			holds_at(F,P0,S),\n"+
					"			not happens_in_between(tick,P0,P,S).\n"+
					"\n"+
					"% (EC13)\n"+
					"not_holds_at_prev_tick(F,P,S):-\n"+
					"         		scenario(S),\n"+
					"			fluent(F),\n"+
					"			timepoint(P),\n"+
					"			timepoint(P0),\n"+
					"			P0<P,\n"+
					"			happens(tick,P0,S),\n"+
					"         		not_holds_at_tick(F,P0,S),\n"+
					"			not happens_in_between(tick,P0,P,S).\n"+
					"% (EC14)\n"+
					"happens_since_last_tick(E,P1,S):-\n"+
					"			event(E),\n"+
					"			scenario(S),\n"+
					"			timepoint(P1),\n"+
					"			timepoint(P0),P0<P1,\n"+
					"			prev_tick(P1,P0,S),\n"+
					"			happens_in_between(E,P0,P1,S).\n"+
					"\n"+
					"% (EC15)\n"+
					"not_happens_since_last_tick(E,P1,S):-\n"+
					"			event(E),\n"+
					"			scenario(S),\n"+
					"			timepoint(P1),\n"+
					"			timepoint(P0),\n"+
					"			P0<P1,\n"+
					"			prev_tick(P1,P0,S),\n"+
					"			not happens_in_between(E,P0,P1,S).\n"+
					"\n"+
					"% (EC16)\n"+
					"happens_in_between(E,P0,P1,S):-\n"+
					"			event(E),\n"+
					"			scenario(S),\n"+
					"			timepoint(P1),\n"+
					"			timepoint(P0),\n"+
					"			P0<P1,\n"+
					"			timepoint(P),\n"+
					"			P0<P,\n"+
					"			P<P1,\n"+
					"			happens(E,P,S).\n"+
					"\n"+
					"% --*** AUXILIARY AXIOMS ***---\n"+
					"\n"+
					"next_tick_at(P1,P2,S):-\n"+
					"		scenario(S),\n"+
					"		timepoint(P1),\n"+
					"		timepoint(P2),\n"+
					"		P1<P2,\n"+
					"		happens(tick,P1,S),\n"+
					"		happens(tick,P2,S),\n"+
					"		not happens_in_between(tick,P1,P2,S).\n"+
					"\n"+
					"prev_tick(P1,P0,S):-\n"+
					"		timepoint(P0),\n"+
					"		timepoint(P1),\n"+
					"		scenario(S),\n"+
					"		P0<P1,\n"+
					"         	happens(tick,P0,S),\n"+
					"		not happens_in_between(tick,P0,P1,S).\n"+
					"\n"+
					"% --*** CONSTRAINTS  ***---\n"+
					"\n"+
					":- timepoint(T),\n"+
					"	event(A1),event(A2),\n"+
					"	A1 != A2, scenario(S),\n"+
					"	executed(A1,T,S),\n"+
					"	executed(A2,T,S).\n"+
					"\n"+
					":- timepoint(T),\n"+
					"	event(A1),event(A2),\n"+
					"    A1 != A2, scenario(S),\n"+
					"	happens(A1,T,S),\n"+
					"	happens(A2,T,S).\n"+
					"\n"+
					":- event(A),scenario(S),timepoint(P),\n"+
					"		happens(A,P,S),\n"+
					"		impossible(A,P,S).\n";
	
	private String modes = 
					"% ----*** MODES ***----\n"+
					"#modeh impossible($sys,+timepoint,+scenario).\n"+
					"\n"+
					"#modeb holds_at_tick($fluent,+timepoint,+scenario).\n"+
					"#modeb not_holds_at_tick($fluent,+timepoint,+scenario).\n"+
					"#modeb holds_at_prev_tick($fluent,+timepoint,+scenario).\n"+
					"#modeb not_holds_at_prev_tick($fluent,+timepoint,+scenario).\n"+
					"#modeb not happens_since_last_tick($sys,+timepoint,+scenario).\n"+
					"#modeb happens_since_last_tick($sys,+timepoint,+scenario).\n"+
					"\n";
	
	
	private boolean error = false;
	HashSet<String> fluentList = new HashSet<String>();
	HashMap<String, HashSet<String>> initiates = new HashMap<String, HashSet<String>>();
	HashMap<String, HashSet<String>> terminates = new HashMap<String, HashSet<String>>();
	HashSet<String> initialValue = new HashSet<String>();
	HashMap<String, HashSet<String>> setList = new HashMap<String, HashSet<String>>();
	HashSet<String> eventList = new HashSet<String>();
	LinkedList<String> constraintLeft = new LinkedList<String>();
	LinkedList<String> constraintRight = new LinkedList<String>();
	LinkedList<String> goalLeft = new LinkedList<String>();
	LinkedList<String> goalRight = new LinkedList<String>();
	HashSet<String> systemList = new HashSet<String>();
	
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
		eventList.add("tick");
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
						if (splits.length == 3){
							splits[0] = splits[1];
							splits[1] = splits[2];
						}
						splits[0] = splits[0].replace(" ", "");
						constraintLeft.addLast(splits[0].replace("(", "").replace(")",""));
						splits[1] = splits[1].substring(splits[1].indexOf('(')+1, splits[1].indexOf(')'));
						constraintRight.addLast(splits[1]);
						tmp = "";
						flag = false;
					}
				}
			}
		}
	}
	
	private void newGoal(String line){
		line = line.split("=")[1];
		
		String[] splits = line.split("->");
		if (splits.length != 3)
			return;
		
		String left = splits[1].replace("(", "").replace(")","").replace(" ", "");
		String right = "";
		splits[2] = splits[2].replace(" ", "");
		Pattern p = Pattern.compile("tick(&&!?\\w+)+");
		Matcher m = p.matcher(splits[2]);
		if (m.find()){
			right = splits[2].substring(m.start(), m.end());
		}
		else{
			p =Pattern.compile("tick&&\\([\\w&|!]+\\)");
			m = p.matcher(splits[2]);
			if (m.find())
				right =  splits[2].substring(m.start(),m.end());
		}
		
		
		right = right.replace("tick&&", "").replace("(", "").replace(")","");
		
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
	
	private void printHoldsAt(BufferedWriter writer, boolean isLast, boolean isPrev, String condition, boolean reverse) throws IOException{
		condition = lowerFirstLetter(condition);
		String result = "";
		if (condition.startsWith("!")){
			result = "\t\tnot_holds_at_tick(" + condition.replace("!", "") +",T,S)";
			if (reverse)
				result = result.replace("not_", "");
		}
		else{
			result = "\t\tholds_at_tick(" + condition +",T,S)";
			if (reverse)
				result = result.replace("holds_at", "not_holds_at");
		}
		
		if (isLast)
	        result = result + ".\n";
	    else
	        result = result + ",\n";
		
		 if (isPrev)
		        result = result.replace("at_tick","at_prev_tick");

	    writer.write(result);	
	}
	
	private void printConstraints(BufferedWriter writer) throws IOException{
		writer.write("% --*** DOMAIN PRECONDITIONS ***---\n");
		
		while(!constraintLeft.isEmpty()){
		
		String left = constraintLeft.pop();
		String right = constraintRight.pop();
		
		left = left.replace("tick&&", "").replace("(", "").replace(")","");
		String[] lefts = left.split("\\|\\|");
		for (int i=0;i<lefts.length;i++)
			System.out.println(lefts[i]);
		
		String[] rights = right.split(" W ");
		for (int i=0;i<rights.length;i++){
			rights[i] = rights[i].replace(" ", "");
		}
		
		for (int i=0;i<lefts.length;i++){
			if (!rights[0].contains("||")){
				String[] rightList = rights[1].split("&&");
				for (int j=0;j<rightList.length;j++){
					writer.write("impossible("+rights[0].replace("!", "")+",T,S):-\n");
					writer.write("\t\tscenario(S),\n");
					writer.write("\t\ttimepoint(T),\n");
					String[] conditionList = lefts[i].split("&&");
					if (rights[0].equals("!tick")){
						for (int k=0;k<conditionList.length;k++){
							printHoldsAt(writer,false,true,conditionList[k],false);
						}
						writer.write("\t\tnot_happens_since_last_tick("+rightList[j]+").\n");
					}
					else{
						for (int k=0;k<conditionList.length;k++){
							printHoldsAt(writer,k==conditionList.length-1,true,conditionList[k],false);
						}
					}
				}
			}
			else{
				String[] rightList = rights[1].split("\\|\\|");
				writer.write("impossible("+rights[0].replace("!", "")+",T,S):-\n");
				writer.write("\t\tscenario(S),\n");
				writer.write("\t\ttimepoint(T),\n");
				String[] conditionList = lefts[i].split("&&");
				if (rights[0].equals("!tick")){
					for (int k=0;k<conditionList.length;k++){
						printHoldsAt(writer,false,true,conditionList[k],false);
					}
					for (int k=0;k<rightList.length;k++){
						if (k==rightList.length-1)
							writer.write("\t\tnot_happens_since_last_tick("+rightList[k]+").\n");
						else
							writer.write("\t\tnot_happens_since_last_tick("+rightList[k]+"),\n");	
					}
				}
				else{
					for (int k=0;k<conditionList.length;k++)
						printHoldsAt(writer,k==conditionList.length-1,true,conditionList[k],false);
				}
			}
		}
		
		}
	}
	
	private void printInitialValue(BufferedWriter writer) throws IOException{
		
		writer.write("% --*** INITIAL STATE ***--\n\n");
		for (String initial:initialValue){
			writer.write("initially("+lowerFirstLetter(initial)+",S):-\n");
			writer.write("\t\tscenario(S).\n");
		}
	}
	
	private void printGoals(BufferedWriter writer) throws IOException{
		
		writer.write("% --*** GOALS ***--\n\n");
		
		while(!goalLeft.isEmpty()){
			String left = goalLeft.pop();
			String right = goalRight.pop();
			String[] leftList = left.split("\\|\\|");
			String[] rightList = right.split("&&");
			
			for (int i=0;i<leftList.length;i++)
				for (int j=0;j<rightList.length;j++){
					String condition[] = leftList[i].split("&&");
					String result[]  = rightList[j].split("\\|\\|");
					
					writer.write(":-scenario(S), timepoint(T),\n");
					for (int k=0; k<result.length;k++){
						printHoldsAt(writer,false,false,result[k],true);
					}
					
					for (int k=0; k<condition.length;k++)
						printHoldsAt(writer, k==result.length-1, true, condition[k], false);
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
		
		/*System.out.println("Fluents:");
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
		}*/
		BufferedWriter writer = null;
		
		try {
			writer = new BufferedWriter(new FileWriter(toDirectory));
			
			writer.write(axiom);
			
			printTypes(writer);
			
			printInitsNTerms(writer);
			
			printConstraints(writer);
			
			printInitialValue(writer);
			
			printGoals(writer);
			
			writer.write(modes);
			
			writer.close();
			
		} catch (IOException e) {
			e.printStackTrace();
		}
		
		
		return true;
	}

}
