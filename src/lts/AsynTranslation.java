package lts;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;
import java.util.HashSet;
import java.util.Stack;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import ui.HPWindow;

public class AsynTranslation {
	private boolean error = false;
	
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
		
		return true;
	}
}
