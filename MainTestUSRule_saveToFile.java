import java.io.IOException;
import java.io.UnsupportedEncodingException;
import java.net.URL;

/**
 * US-Rule: Discovering utility-driven sequential rules, 
 * Gengsen Huang, Wensheng Gan, Jian Weng, Philip S. YU,
 * ACM Transactions on Knowledge Discovery from Data, 2022
 * 
 *  This example files shows how to run the US-Rule algorithm.
 *  @author Gengsen Huang, 2021.
 */
public class MainTestUSRule_saveToFile {
	
	public static void main(String [] arg) throws IOException{
		// input file
		String input = fileToPath("data.txt"); 
		// output file
		String output = "./output.txt";  

		// the minimum confidence threshold
		double minconf = 0.4;

		// the minimum utility threshold
		double minutil = 10;
				

		// the maximum size of the antecedent of a sequential rule
		int maxAntecedentSize = 5;
		// the maximum size of the consequent of a sequential rule
		int maxConsequentSize = 5;
		
		// This parameter let the user specify how many sequences from the input file should be used.
		int maximumSequenceCount = Integer.MAX_VALUE;
		
		// This create the algorithm and run it.
		// Results will be output to the file.
		AlgoUSRule algo = new AlgoUSRule ();
		algo.runAlgorithm(input, output, minconf, minutil, maxAntecedentSize, maxConsequentSize, maximumSequenceCount);
		
		// print statistics
		algo.printStats();
	}
	
	public static String fileToPath(String filename) throws UnsupportedEncodingException{
		URL url = MainTestUSRule_saveToFile.class.getResource(filename);
		 return java.net.URLDecoder.decode(url.getPath(),"UTF-8");
	}
}
