import java.util.*;
import java.util.Map.Entry;
import java.util.stream.Collectors;
import java.io.*;

class ScriptGen {

  static List<String> script_lines = new ArrayList<String>();
  static Map<String, Set<String>> actors = new HashMap<String,Set<String>>();

  static public void print(PrintWriter writer) { 
    writer.println("#"); writer.println(load_policy());
    writer.println("##"); refine(writer); 
    writer.println("###"); init(writer); 
    writer.println("####");
    for (String line : script_lines) {
      writer.println(line);
    }
    writer.close();
  }

  static private String load_policy()  {
    try {
      Scanner sc = new Scanner(new File("spec.frames")); 
      sc.useDelimiter("\\Z"); 
      return sc.next();
    }catch(FileNotFoundException e) {
      System.out.println("file not found");
      System.exit(1);
    }  
    return null;
  }

  static private void refine(PrintWriter writer) {
    for (Entry<String, Set<String>> entry : actors.entrySet()) {
      writer.print("Fact " + entry.getKey() + " Identified by [");
      writer.print(entry.getValue().stream().collect(Collectors.joining(",")));
      writer.println("]");
    }
    writer.println("Fact administrator Identified by Admin");
  }

  static private void init(PrintWriter writer) {
    writer.println("administrator. citizen. candidate. enable vote(Admin,citizen). declare winner.");
  }

  static public void add_actor(String actor, String type) {
    actors.putIfAbsent(type, new HashSet<String>());
    actors.get(type).add(actor);
  }

  static public void enable_vote(String citizen) {
    script_lines.add("!enable vote(Admin, " + citizen + ").");
  }

  static public void cast_vote(String voter, String candidate) {
    script_lines.add("!cast vote(voter(" + voter + "),Admin," + candidate +").");
  } 

  static public void declare_winner(String winner) {
    script_lines.add("!declare winner(Admin, " + winner + ").");
  }
}
