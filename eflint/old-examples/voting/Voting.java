import java.util.*;
import java.util.Map.Entry;
import java.util.stream.Collectors;
import java.io.*;

class Voting {
  Set<String> registered_voters = new HashSet<String>();
  Map<String,Integer> vote_count = new HashMap<String, Integer>();

  public Voting() { }
 
  public void register_voter(String name) {
    registered_voters.add(name);
    // qualification
    ScriptGen.add_actor(name, "citizen");
    ScriptGen.enable_vote(name);
  }

  public void register_candidate(String name) {
    vote_count.put(name,0);
    // qualification
    ScriptGen.add_actor(name, "candidate");
  }

  public void vote(String voter, String candidate) {
    vote_count.put(candidate, vote_count.getOrDefault(candidate,0) + 1);
    // qualification
    ScriptGen.cast_vote(voter, candidate);
  }

  // returns null if there is no winner
  public String find_winner() {
    String winner = null;
    int winning_votes = 0;
    for (Entry<String,Integer> entry : vote_count.entrySet()) {
      if(entry.getValue() > winning_votes) {
        winner = entry.getKey();
        winning_votes = entry.getValue();
      }
    }
    // qualification
    if (winner != null) {
      ScriptGen.declare_winner(winner);
    }
    return winner;
  }
}  

class Fail0 { // fails because an unregistered voter has voted
  public static void main(String[] args) throws IOException {
    Voting voting = new Voting();
    voting.register_candidate("Chloe");
    voting.register_candidate("David");
    voting.register_voter("Alice");
    voting.register_voter("Bob");
    voting.vote("Alice", "Chloe");
    voting.vote("Bob", "Chloe");
    voting.vote("John", "Chloe");
    System.out.println("winner is: " + voting.find_winner());
    ScriptGen.print(new PrintWriter(new FileWriter(new File(args[0]))));
  }
}

class Fail1 { // fails because Alice votes twice
  public static void main(String[] args) throws IOException {
    Voting voting = new Voting();
    voting.register_candidate("Chloe");
    voting.register_candidate("David");
    voting.register_voter("Alice");
    voting.register_voter("Bob");
    voting.register_voter("John");
    voting.vote("Bob", "David");
    voting.vote("John", "David");
    voting.vote("Alice", "Chloe");
    voting.vote("Alice", "Chloe");
    System.out.println("winner is: " + voting.find_winner());
    ScriptGen.print(new PrintWriter(new FileWriter(new File(args[0]))));
  }
}

class Fail2 { // fails because John has not voted yet
  public static void main(String[] args) throws IOException { 
    Voting voting = new Voting();
    voting.register_candidate("Chloe");
    voting.register_candidate("David");
    voting.register_voter("Alice");
    voting.register_voter("Bob");
    voting.register_voter("John");
    voting.vote("Alice", "Chloe");
    voting.vote("Bob", "David");
    System.out.println("winner is: " + voting.find_winner());
    ScriptGen.print(new PrintWriter(new FileWriter(new File(args[0]))));
  }
}

class Fail3 { // fails because Chloe and David have equal amount of votes
  public static void main(String[] args) throws IOException {
    Voting voting = new Voting();
    voting.register_candidate("Chloe");
    voting.register_candidate("David");
    voting.register_voter("Alice");
    voting.register_voter("Bob");
    voting.register_voter("John");
    voting.register_voter("Frank");
    voting.vote("Alice", "Chloe");
    voting.vote("Bob", "David");
    voting.vote("John", "David");
    voting.vote("Frank", "Chloe");
    System.out.println("winner is: " + voting.find_winner());
    ScriptGen.print(new PrintWriter(new FileWriter(new File(args[0]))));
  }
}

class Success1 {
  public static void main(String[] args) throws IOException {
    Voting voting = new Voting();
    voting.register_candidate("Chloe");
    voting.register_candidate("David");
    voting.register_voter("Alice");
    voting.register_voter("Bob");
    voting.register_voter("John");
    voting.vote("Alice", "Chloe");
    voting.vote("Bob", "David");
    voting.vote("John", "David");
    System.out.println("winner is: " + voting.find_winner());
    ScriptGen.print(new PrintWriter(new FileWriter(new File(args[0]))));
  }
}
