import java.io.BufferedWriter;
import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.BitSet;
import java.util.Collections;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

/**
 * US-Rule: Discovering utility-driven sequential rules, 
 * Gengsen Huang, Wensheng Gan, Jian Weng, Philip S. YU,
 * ACM Transactions on Knowledge Discovery from Data, 2022
 * 
 * US-Rule_{V4}: Using REUCP, REURP, and four pruning strategies associated with upper bounds.
 * This is the implementation of the US-Rule_{V4} algorithm.
 * Part of the code is from HUSRM (Efficient Mining of High Utility Sequential Rules).
 * Thanks to the authors of HUSRM for the open source code.
 * 
 * @author Gengsen Huang, 2021
 */
public class AlgoUSRule {
	// for statistics 
	/** start time of latest execution */
	long timeStart = 0; 
	/** end time of latest execution */
	long timeEnd = 0; 
	/**  number of rules generated */
	int ruleCount; 

	// parameters 
	/** minimum confidence **/
	double minConfidence;
	
	/** minimum support */
	double minutil;

	/** this is the sequence database */
	SequenceDatabaseWithUtility database;

	/** this buffered writer is used to write the output file */
	BufferedWriter writer = null;
	
	/** this is a map where the KEY is an item and the VALUE is the list of sequences
	/* containing the item. */
	private Map<Integer, ListSequenceIDs> mapItemSequences;
	
	/** the maximum size of the antecedent of a sequential rule */
	private int maxSizeAntecedent;
	
	/** the maximum size of the antecedent of a sequential rule */
	private int maxSizeConsequent;
	
	/** the maximum times of using REURP */
	private int maximumRemoveTimes = Integer.MAX_VALUE;
	
	/** Strategy 1: remove items with a sequence estimated utility < minutil */
	private boolean deactivateStrategy1 = false;  
	
	/** Strategy 2: remove rules contains two items a--> b with a sequence estimated utility < minutil */
	private boolean deactivateStrategy2 = false; 
	
	/** use bitvectors instead of array list for quickly calculating the support of a rule antecedent */
	private boolean bitvectorOptimization = false;  
	
	private Map<Integer, HashMap<Integer, Double>> REUCM;
	
	/** the count of expansions */
	private long expandCount = 0;
	
	/**
	 * Default constructor
	 */
	public AlgoUSRule() {
	}
	
    /**
	 * This is a structure to store some estimated utility and a list of sequence ids.
	 * It will be used in the code for storing the estimated utility of a rule and the list
	 * of sequence ids where the rule appears.
	 */
	public class EstimatedUtilityAndSequences{
		// an estimated profit value
		Double utility = 0d;
		// a list of sequence ids
		List<Integer> sequenceIds = new ArrayList<Integer>();
	}
	


	/**
	 * The main method to run the algorithm
	 * 
	 * @param input an input file
	 * @param output an output file
	 * @param minConfidence the minimum confidence threshold
	 * @param minutil the minimum utility threshold
	 * @param maxConsequentSize a constraint on the maximum number of items that the right side of a rule should contain
	 * @param maxAntecedentSize a constraint on the maximum number of items that the left side of a rule should contain
	 * @param maximumNumberOfSequences the maximum number of sequences to be used
	 * @exception IOException if error reading/writing files
	 */
	//@SuppressWarnings("unused")
	public void runAlgorithm(String input, String output,
			double minConfidence, double minutil, int maxAntecedentSize, int maxConsequentSize, 
			int maximumNumberOfSequences) throws IOException {
		
		// save the minimum confidence parameter
		this.minConfidence = minConfidence;
		
		// save the constraints on the maximum size of left/right side of the rules
		this.maxSizeAntecedent  = maxAntecedentSize;
		this.maxSizeConsequent  = maxConsequentSize;
		
		// reinitialize the number of rules found
		ruleCount = 0;
		this.minutil = minutil;

		// if the database was not loaded, then load it.
		if (database == null) {
			try {
				database = new SequenceDatabaseWithUtility();
				database.loadFile(input, maximumNumberOfSequences);
			} catch (Exception e) {
				e.printStackTrace();
			}
		}
		
		// We reset the tool for calculating the maximum memory usage
		MemoryLogger.getInstance().reset();

		// we prepare the object for writing the output file
		writer = new BufferedWriter(new FileWriter(output));

		// if minutil is 0, set it to 0.001 to avoid generating
		// all rules 
		this.minutil = minutil;
		if (this.minutil == 0) { 
			this.minutil = 0.001;
		}

		// save the start time
		timeStart = System.currentTimeMillis(); 
	
		// we use these two variables to utilize REURP
		int removeCount = 0;
		int removeTimes = 0;
		
		
		// if this strategy has not been deactivated
		if(deactivateStrategy1 == false){
			// This map will store pairs of (key: item, value: estimated profit of the item)
			Map<Integer, Double> mapItemEstimatedUtility = new HashMap<Integer, Double>();
			 
			// We read the database.
			// For each sequence 
			for (SequenceWithUtility sequence : database.getSequences()) {
				// for each itemset in that sequence
				for (List<Integer> itemset : sequence.getItemsets()) {
					// for each item
					for (Integer item : itemset) {
						// get the current sequence estimated utility of that item
						Double estimatedUtility = mapItemEstimatedUtility.get(item);									
						// if we did not see that item yet
						if  (estimatedUtility == null)    {
							// then its estimated utility of that item until now is the 
							// utility of that sequence
							estimatedUtility = sequence.exactUtility;			 
						} else {
							// otherwise, it is not the first time that we saw that item
							// so we add the utility of that sequence to the sequence
							// estimated utility f that item
							estimatedUtility = estimatedUtility + sequence.exactUtility;
						}
						// update the estimated utility of that item in the map
						mapItemEstimatedUtility.put(item, estimatedUtility);
					}
				}
			}
	
			// we create an iterator to loop over all items
			Iterator<Entry<Integer, Double>> iterator = mapItemEstimatedUtility.entrySet().iterator();
			// for each item
			while (iterator.hasNext()) {
				
				// we obtain the entry in the map
				Map.Entry<java.lang.Integer, java.lang.Double> entryMapItemEstimatedUtility 
					= (Map.Entry<java.lang.Integer, java.lang.Double>) iterator.next();
				Double estimatedUtility = entryMapItemEstimatedUtility.getValue();
				
				// if the estimated utility of the current item is less than minutil
				if (estimatedUtility < minutil) {
					removeCount++;
					// we remove the item from the map
					iterator.remove();
				}
			}
			
			// Total utility of items to be removed 
			double removeUtility = 0;
			
			while(removeTimes < maximumRemoveTimes) {
				// If not item can be removed
				if(removeCount == 0) {
					break;
				}
				// update removeTimes
				removeTimes++;
				removeCount = 0;
				// scan the database again.
				// For each sequence
				Iterator<SequenceWithUtility> iteratorSequence = database.getSequences().iterator();
				while (iteratorSequence.hasNext()) {
					
					SequenceWithUtility sequence = iteratorSequence.next();
					// Initialize to 0
					removeUtility = 0;
					
					// For each itemset
					Iterator<List<Integer>> iteratorItemset = sequence.getItemsets().iterator(); 
					Iterator<List<Double>> iteratorItemsetUtilities = sequence.getUtilities().iterator();
					while (iteratorItemset.hasNext()) {
						// the items in that itemset
						List<java.lang.Integer> itemset = iteratorItemset.next();
						// the utility values in that itemset
						List<java.lang.Double> itemsetUtilities = iteratorItemsetUtilities.next();
						
						// Create an iterator over each item in that itemset
						Iterator<Integer> iteratorItem = itemset.iterator();
						// Create an iterator over utility values in that itemset
						Iterator<Double> iteratorItemUtility = itemsetUtilities.iterator();

						// For each item
						while (iteratorItem.hasNext()) {
							// get the item 
							Integer item = iteratorItem.next();
							// get its utility value
							Double utility = iteratorItemUtility.next();
							 
							// if the item is unpromising
							if(mapItemEstimatedUtility.get(item) == null){
							
								// remove the item
								iteratorItem.remove();
								// remove its utility value
								iteratorItemUtility.remove();
								// subtract the item utility value from the sequence utility.
								sequence.exactUtility -= utility;
								// update removeUtility
								removeUtility += utility;						
							}
						}
						
						// If the itemset has become empty, we remove it from the sequence
						if(itemset.isEmpty()){
							iteratorItemset.remove();
							iteratorItemsetUtilities.remove();
						}
					}
					
					// If the sequence has become empty, we remove the sequences from the database
					if(sequence.size() == 0){
						iteratorSequence.remove();
					}else {
						// update the SEU of all items
						iteratorItemset = sequence.getItemsets().iterator(); 
						while (iteratorItemset.hasNext()) {
							// the items in that itemset
							List<java.lang.Integer> itemset = iteratorItemset.next();
							
							// Create an iterator over each item in that itemset
							Iterator<Integer> iteratorItem = itemset.iterator();
							
							// For each item
							while (iteratorItem.hasNext()) {
								// get the item 
								Integer item = iteratorItem.next();
								// Update the SEU of this item and determine if it should be removed
								if(mapItemEstimatedUtility.get(item) - removeUtility < minutil) {
									 removeCount++;
									 mapItemEstimatedUtility.remove(item);
								}else {
									 mapItemEstimatedUtility.put(item, mapItemEstimatedUtility.get(item) - removeUtility);
								}
							}
							
						}
					}
				}
			}

		}
		

		// We create a map to store for each item, the list of sequences containing the item
		// Key: an item, Value:  the list of sequences containing the item
		mapItemSequences = new HashMap<Integer, ListSequenceIDs>();
		
		// For each sequence
		for (int i=0; i < database.getSequences().size(); i++){
			SequenceWithUtility sequence = database.getSequences().get(i);
			
			// For each itemset
			for (List<Integer> itemset : sequence.getItemsets()) {
				
				// For each item
				for (Integer item : itemset) {
					// Get the list of identifiers of sequence containing that item
					ListSequenceIDs numerosSequenceItem = mapItemSequences.get(item);
					
					// If the list does not exist, we will create it
					if(numerosSequenceItem == null){
						// if the user desactivated strategy 3, we will use an arraylist implementation
						if(bitvectorOptimization){
							numerosSequenceItem = new ListSequenceIDsArrayList();
						}else{
							// otherwise we use a bitvector implementation, which is more efficient
							numerosSequenceItem = new ListSequenceIDsBitVector();
						}
						// we add the list in the map for that item
						mapItemSequences.put(item, numerosSequenceItem);
					}
					// finally we add the current sequence ids to the list of sequences ids of the current
					// item
					numerosSequenceItem.addSequenceID(i);
				}
			}
		}

		
		// We create a map of map to store the estimated utility and list of sequences ids for
		// each rule of two items (e.g. a -> b  ).
		// The key of the first map: the item "a" in the left side of the rule
		// The key of the second map:  the item "b" in the right side of the rule
		// The value in the second map:  the estimated utility of the rule and sequence ids for that rule
		Map<Integer,Map<Integer, EstimatedUtilityAndSequences>> mapItemItemEstimatedUtility = new HashMap<Integer,Map<Integer, EstimatedUtilityAndSequences>>();
		REUCM = new HashMap<Integer, HashMap<Integer, Double>>();
		
		// For each sequence
		for (int z = 0; z < database.getSequences().size(); z++) {
			SequenceWithUtility sequence = database.getSequences().get(z);
			// For each itemset I 
			for (int i = 0; i< sequence.getItemsets().size(); i++) {
				// get the itemset
				List<Integer> itemset = sequence.getItemsets().get(i);
				// For each item  X 
				for (int j = 0; j < itemset.size(); j++) {
					Integer itemX = itemset.get(j);
					for(int t = j+1; t < itemset.size(); t++) {
						HashMap<Integer, Double> mapA = REUCM.get(itemX);
						if(mapA == null) {
							mapA = new HashMap<Integer, Double>();
							mapA.put(itemset.get(t), sequence.exactUtility);
							REUCM.put(itemX, mapA);
						}else {
							if(mapA.get(itemset.get(t)) == null) {
								mapA.put(itemset.get(t), sequence.exactUtility);
							}else {
								mapA.put(itemset.get(t), sequence.exactUtility+mapA.get(itemset.get(t)));
							}
							REUCM.put(itemX, mapA);
						}
					}

					// For each item Y occuring after X,
					// that is in the itemsets I+1, I+2 .... 
					for (int k = i+1; k < sequence.getItemsets().size(); k++) {
						//  for a given itemset K
						List<Integer> itemsetK = sequence.getItemsets().get(k);
						// for an item Y
						for(Integer itemY : itemsetK){
							// Update REUCP(itemX, itemY)
							// They are not in the same itemset
							HashMap<Integer, Double> mapA = REUCM.get(itemX);
							if(mapA == null) {
								mapA = new HashMap<Integer, Double>();
								mapA.put(itemY, sequence.exactUtility);
								REUCM.put(itemX, mapA);
							}else {
								if(mapA.get(itemY) == null) {
									mapA.put(itemY, sequence.exactUtility);
								}else {
									mapA.put(itemY, sequence.exactUtility+mapA.get(itemY));
								}
								REUCM.put(itemX, mapA);
							}
							
							
							// Get the map for item X
							Map<Integer, EstimatedUtilityAndSequences> mapXItemUtility = mapItemItemEstimatedUtility.get(itemX);
							
							// If we never saw X before
							if(mapXItemUtility == null){
								// we create a map for X
								mapXItemUtility = new HashMap<Integer, EstimatedUtilityAndSequences>();
								mapItemItemEstimatedUtility.put(itemX, mapXItemUtility);
								
								// Then we create a structure for storing the estimated utility of X ->Y
								EstimatedUtilityAndSequences structure = new EstimatedUtilityAndSequences();
								structure.utility = sequence.exactUtility; // the current sequence utility
								structure.sequenceIds.add(z); // the sequence id
								// add it in the map for X -> Y
								mapXItemUtility.put(itemY, structure);
							}
							else{
								// in the case were we saw X before.
								// We get its structure for storing the estimated utility of X -> Y
								EstimatedUtilityAndSequences structure = mapXItemUtility.get(itemY);
								// if we never saw X ->Y
								if(structure == null){

									// Then we create a structure for storing the estimated utility of X ->Y
									structure = new EstimatedUtilityAndSequences(); 
									structure.utility = sequence.exactUtility; // the current sequence utility
									structure.sequenceIds.add(z); // the sequence id

									// add it in the map for X -> Y
									mapXItemUtility.put(itemY, structure);
								}else{
									// if we saw X -> Y before
									// We add the sequence utility to the utility of that rule
									structure.utility = structure.utility + sequence.exactUtility;
									// We add the sequence ids to the list of sequence ids of that rule.
									structure.sequenceIds.add(z);
								}
							}	
							
						}	
					}
				}
			}
		}
		
		// Remove mappings smaller than minutil 
		for(Iterator it = REUCM.keySet().iterator(); it.hasNext();) {
			int a = (int) it.next();
			Iterator<Entry<Integer, Double>> iterator = REUCM.get(a).entrySet().iterator();
			// for each item
			while (iterator.hasNext()) {
				
				// we obtain the entry in the map
				Map.Entry<java.lang.Integer, java.lang.Double> entryMapItemEstimatedUtility 
					= (Map.Entry<java.lang.Integer, java.lang.Double>) iterator.next();
				Double estimatedUtility = entryMapItemEstimatedUtility.getValue();
				
				// if the estimated utility of the current item is less than minutil
				if (estimatedUtility < minutil) {
					// we remove the item from the map
					iterator.remove();
				}
			}
		}

		
		// Remove mappings smaller than minutil 
		// For each entry in the map
		for(Entry<Integer, Map<Integer, EstimatedUtilityAndSequences>> mapI : mapItemItemEstimatedUtility.entrySet()){
		
			// An entry represents an item "i" (the key) and some maps (value)
			// We will loop over the entries of the secondary map of "i" (value)
			// to remove all rules of the form i -> j where the estimated utility
			// is lower than minutil
			
			// Create an iterator
			Iterator<Entry<Integer, EstimatedUtilityAndSequences>> iterEntry = 	mapI.getValue().entrySet().iterator();
			
			// loop over the map
			while (iterEntry.hasNext()) {
				// We consider each entry j and the estimated utility of i-> j
				Map.Entry<java.lang.Integer, EstimatedUtilityAndSequences> entry = (Map.Entry<java.lang.Integer, EstimatedUtilityAndSequences>) iterEntry
						.next();
				// if the estimated profit of i -> j is lower than minutil
				// we remove that rule because no larger rule containing that rule
				// can have a estimated utility higher or equal to minutil.
				if(entry.getValue().utility < minutil){
					// we only do that if the user did not deactivate strategy 2
					if(deactivateStrategy2 == false){
						iterEntry.remove();
					}
				}
				
			}
		}
		

		// generate 1*1 rules
		// For each rule X --> Y
		for(Entry<Integer, Map<Integer, EstimatedUtilityAndSequences>> entryX : mapItemItemEstimatedUtility.entrySet()){
			// Get the item X
			Integer itemX = entryX.getKey();
			
			// Get the list of sequence ids containing the item X
			ListSequenceIDs sequenceIDsX =  mapItemSequences.get(itemX);
			// Get the support of item X
			double supportX = sequenceIDsX.getSize();
			
			// For each Y
			for(Entry<Integer, EstimatedUtilityAndSequences> entryYUtility : entryX.getValue().entrySet()){
				Integer itemY = entryYUtility.getKey();
				
				// Get the estimated utility and list of sequences ids for the rule X -> Y
				EstimatedUtilityAndSequences structure = entryYUtility.getValue();
				List<Integer> sequencesIDsXY = structure.sequenceIds;
				
				// Get the support of the rule X -> Y
				double supportXY = sequencesIDsXY.size();
				
				// We create the RE-table of rule X -> Y
				REtable table = new REtable();
				
				// We will scan each sequence to fill the RE-table 
				// and update the other variable to calculate the confidence of the rule.
				
				// for each sequence containing X -> Y
				for(Integer numeroSequence : sequencesIDsXY){
					// Get the sequence
					SequenceWithUtility sequence = database.getSequences().get(numeroSequence);
	
					// Create a new element in the table
					ElementREtable element = new ElementREtable(numeroSequence);
					
					// we reset position alpha and beta
					int positionAlphaItem =-1;
					int positionBetaItem =-1;
	
					// For each itemset I 
		loop1:		for (int i = 0; i< sequence.getItemsets().size(); i++) {
						// get the itemset I
						List<Integer> itemset = sequence.getItemsets().get(i);
						
						// For each item J
						for (int j=0; j < itemset.size(); j++) {
							Integer itemIJ = itemset.get(j);
							
							// if we found the item X
							if(itemX.equals(itemIJ)){
								// we get its utility
								double utilityXPositionIJ = sequence.getUtilities().get(i).get(j);
								// we add it to the exact utility in the current RE-table element
								element.utility += utilityXPositionIJ;
								
								// Stop and remember that position
								element.positionAlphaItemset = i;
								// remember the position ALPHA (which in this case means where the item in 
								// the right side
								// of a rule was found)
								positionAlphaItem = j;
								
								// since we found j, we don't need to continue this loop since we assume
								// that an item do not occur more than once per sequence
								break loop1;
							}else if(itemIJ > itemX){
								// If the item is greater than the item X,
								// we add the profit of this item to the ULeft value of its element.
								double profitXPositionIJ = sequence.getUtilities().get(i).get(j);
								element.ULeft += profitXPositionIJ;
							}
						}
					}
		 			
					// If X does not appear, we don't do the following steps
					if(element.positionAlphaItemset == -1){
						continue;
					}
					
					// for each itemset starting from the last one until itemset alpha+1
		loop2:	for (int i = sequence.getItemsets().size()-1; 
						i >  element.positionAlphaItemset ; i--) {
						// get the current itemset
						List<Integer> itemset = sequence.getItemsets().get(i);
	
						// for each item J in that itemset
						for (int j = itemset.size() -1; j >= 0; j--) {
							// get the item J
							Integer itemIJ = itemset.get(j);
	
							// if that item is Y
							if(itemY.equals(itemIJ))
							 {		 
								// we add Y's profit to the exact utility of the current element
								double profitYPositionIJ = sequence.getUtilities().get(i).get(j);
								element.utility += profitYPositionIJ;
								
								// we stop and remember that we stopped at the i-th itemset
								// we will call this position "beta".
								element.positionBetaItemset = i;
								positionBetaItem= j;
	
								break loop2;
							 }else if(itemIJ > itemY){
								// If the item is greater than the item Y,
								// we add the profit of this item to the URight value of its element.
								double profitXPositionIJ = sequence.getUtilities().get(i).get(j);
								element.URight += profitXPositionIJ;
							}
						}
					}
					/// If Y does not appear, we don't do the following steps
					 if(element.positionBetaItemset == -1){
						 continue;
					 } 

					List<Integer> itemsetAlpha = sequence.getItemsets().get(element.positionAlphaItemset);
					// FOR EACH ITEM J IN THE ALPHA ITEMSET
					for (int j = positionAlphaItem + 1; j < itemsetAlpha.size(); j++) {

						// we add the utility of the item to the ULeft value of the current element.
						double profitPositionIJ = sequence.getUtilities().get(element.positionAlphaItemset).get(j);
						element.ULeft += profitPositionIJ;
					}
	
					for (int i = element.positionAlphaItemset+1; i < element.positionBetaItemset; i++) {
							// get the itemset
							List<Integer> itemset = sequence.getItemsets().get(i);
	
							// For each item J
							for (int j=0; j < itemset.size(); j++) {
								Integer itemIJ = itemset.get(j);
	
								// if the item is greater than X and Y
								if( itemIJ > itemX && itemIJ > itemY ){
									// it means that this item could be used to extend the left or right side
									// of the rule
									// We add its utility to ULeftRight
									double utilityPositionIJ = sequence.getUtilities().get(i).get(j);
									element.ULeftRight += utilityPositionIJ;
								}else if( itemIJ > itemX){
									// if the item is only greater than X
									// We add its utility to ULeft
									double utilityPositionIJ = sequence.getUtilities().get(i).get(j);
									element.ULeft += utilityPositionIJ;
								}else if( itemIJ > itemY){
									// if the item is only greater than Y
									// We add its utility to URight
									double utilityPositionIJ = sequence.getUtilities().get(i).get(j);
									element.URight += utilityPositionIJ;
								}
							}
					 }

					List<Integer> itemset = sequence.getItemsets().get(element.positionBetaItemset);
					
					// For each item J after the beta item (i.e. the item Y)
					for (int j=0; j < positionBetaItem - 1; j++) {
						Integer itemIJ = itemset.get(j);
	
						// if the item is greater than Y
						if( itemIJ > itemY){
							// We add its utility to URight
							double profitPositionIJ = sequence.getUtilities().get(element.positionBetaItemset).get(j);
							element.URight += profitPositionIJ;
						}
					}
	
					element.calculateREEU();
					
					// Finally, we add the element of this sequence to the RE-table of X->Y
					table.addElement(element);
	
			}
				
				// We calculate the confidence of X -> Y
				double confidence = (supportXY / supportX);
				
				// conditions for deciding whether to expand
				double conditionExpandLeft;
				double conditionExpandRight;
	
				// use LEEU and REEU as two conditions
				conditionExpandLeft = table.LEEU;
				conditionExpandRight = table.REEU;
	
				// create the rule antecedent and consequence
				int [] antecedent =  new int[]{itemX};
				int []  consequent =  new int[]{itemY};
				
				// if high utility with high confidence
				if((table.totalUtility >= minutil) && confidence >= minConfidence){
					// we output the rule
					saveRule(antecedent, consequent, table.totalUtility, supportXY, confidence);
				}
				
				// if the right side size is less than the maximum size, we will try to expand the rule
				if(conditionExpandRight >= minutil && maxConsequentSize > 1){
					expandRight(table, antecedent, consequent, sequenceIDsX);
				}
				
				// if the left side size is less than the maximum size, we will try to expand the rule
				if(conditionExpandLeft >= minutil  && maxAntecedentSize > 1){
					expandFirstLeft(table, antecedent, consequent, sequenceIDsX);
				}
			}
		}
		

		//We will check the current memory usage
		MemoryLogger.getInstance().checkMemory();

		// save end time
		timeEnd = System.currentTimeMillis();

		// close the file
		writer.close();

		// after the algorithm ends, we don't need a reference to the database
		// anymore.
		database = null;
	}

	/**
	 * This method save a rule to the output file
	 * @param antecedent the left side of the rule
	 * @param consequent the right side of the rule
	 * @param utility the rule utility
	 * @param support the rule support
	 * @param confidence the rule confidence
	 * @throws IOException if an error occurs when writing to file
	 */
	private void saveRule(int[] antecedent, int[] consequent,
			double utility, double support, double confidence) throws IOException {

		// increase the number of rule found
		ruleCount++;

		// create a string buffer
		StringBuilder buffer = new StringBuilder();

		// write the left side of the rule (the antecedent)
		for (int i = 0; i < antecedent.length; i++) {
			buffer.append(antecedent[i]);
			if (i != antecedent.length - 1) {
				buffer.append(",");
			}
		}

		// write separator
		buffer.append("	==> ");

		// write the right side of the rule (the consequent)
		for (int i = 0; i < consequent.length; i++) {
			buffer.append(consequent[i]);
			if (i != consequent.length - 1) {
				buffer.append(",");
			}
		}
		// write support
		buffer.append("\t#SUP: ");
		buffer.append(support);
		// write confidence
		buffer.append("\t#CONF: ");
		buffer.append(confidence);
		buffer.append("\t#UTIL: ");
		buffer.append(utility);
		writer.write(buffer.toString());
		writer.newLine();
		
	}

	/**
	 * This method is used to create new rule(s) by adding items to the right side of a rule
	 * @param table the RE-table of the rule
	 * @param antecedent the rule antecedent
	 * @param consequent the rule consequent
	 * @param sequenceIdsAntecedent the list of ids of sequences containing the left side of the rule
	 * @throws IOException if an error occurs while writing to file
	 */
	private void expandRight(REtable table, int[] antecedent,
			int[] consequent, ListSequenceIDs sequenceIdsAntecedent) throws IOException {
		
		expandCount++;
		
		// We first find the largest item in the left side and right side of the rule
		int largestItemInAntecedent = antecedent[antecedent.length -1];
		int largestItemInConsequent = consequent[consequent.length -1];
		
		// We create a new map where we will build the RE-table for the new rules that
		// will be created by adding an item to the current rule.
		// Key: an item appended to the rule     Value: the RE-table of the corresponding new rule
		Map<Integer, REtable> mapItemsTables = new HashMap<Integer, REtable>();
		
		// initialize the RSU-table
		Map<Integer, Double> RSUTable = new HashMap<Integer, Double>();
		

		// for each sequence containing the original rule (according to its RE-table)
		for(ElementREtable element : table.elements){
			// update RRSU
			table.REEU -= element.REEU;
			
			// if no items can be expanded
			// we do not need to scan this sequence.
			if(element.ULeft + element.URight + element.ULeftRight  == 0){
				continue;
			}
			
			// Get the sequence
			SequenceWithUtility sequence = database.getSequences().get(element.numeroSequence);
			
			for(int i = element.positionBetaItemset; i < sequence.size(); i++){
				// get the itemset
				List<Integer> itemsetI = sequence.getItemsets().get(i);
				
				// For each item
				for(int j=0; j < itemsetI.size(); j++){
					Integer itemJ = itemsetI.get(j);
				
					// Check if the item is greater than items in the consequent of the rule 
					// according to the lexicographical order 
					if(itemJ <= largestItemInConsequent){
						// if not, then we continue because that item cannot be added to the rule
						continue;
					}
					
					// use REUCP
					if(REUCM.get(largestItemInAntecedent).get(itemJ) == null) {
						continue;
					}
					
					
					// update RSU-table
					if(RSUTable.get(itemJ) == null) {
						RSUTable.put(itemJ, element.REEU);
					}else {
						RSUTable.put(itemJ, element.REEU + RSUTable.get(itemJ));
					}
					
					// use RERSUP
					if(RSUTable.get(itemJ) + table.REEU < minutil) {
						continue;
					}
					
					
					// update the RE-table of the item
					// Get the RE-table of the item
					REtable tableItemJ = mapItemsTables.get(itemJ);
					if(tableItemJ == null){
						// if no RE-table, we create one
						tableItemJ = new REtable();
						mapItemsTables.put(itemJ, tableItemJ);
					}
					
					// We will add a new element in the RE-table
					ElementREtable newElement = new ElementREtable(element.numeroSequence);
  
					// We will update the utility by adding the utility of item J
					double profitItemJ = sequence.getUtilities().get(i).get(j);
					newElement.utility = element.utility + profitItemJ;
					
					// we will copy the ULeft value from the original rule
					newElement.ULeft = element.ULeft;
					
					// we will copy the ULeftRight value from the original rule
					newElement.ULeftRight = element.ULeftRight;
					
					// we will copy the URight value from the original rule
					// but we will subtract the utility of the item J
					newElement.URight = element.URight - profitItemJ;

					// we will copy the position of Alpha and Beta in that sequences because it
					// does not change
					newElement.positionBetaItemset = element.positionBetaItemset; 
					newElement.positionAlphaItemset = element.positionAlphaItemset; 
					
					// Then, we will scan itemsets after the beta position in the sequence
					// We will subtract the utility of items that are smaller than item J 
					// according to the lexicographical order from URight because they
					// cannot be added anymore to the new rule.
					
					// for each such itemset
					for(int z = element.positionBetaItemset; z < sequence.size(); z++){
						List<Integer> itemsetZ = sequence.getItemsets().get(z);
						
						// for each item W
						for(int w= itemsetZ.size()-1; w >= 0 ; w--){
							// 
							// if the item is smaller than the larger item in the right side of the rule
							Integer itemW = itemsetZ.get(w);
							if(itemW <= largestItemInConsequent){
								// we break;
								break; 
							}
			
							// otherwise, if item W is smaller than item J
							 if(itemW < itemJ ){
								// We will subtract the utility of W from URight
								double profitItemW = sequence.getUtilities().get(z).get(w);
								newElement.URight -= profitItemW;
							}
						}
					}
					
					// calculate the REEU of the rule in this ElementREtable
					newElement.calculateREEU();
			
					// Now that we have created the element for that sequence and that new rule
					// , we will add the RE-table of that new rule
					tableItemJ.addElement(newElement);
				}
			}

			int sumULeftRightUntilBetaPrime = 0;
			int sumUtilityLeftUntilBetaPrime = 0;
			
			// For each itemset from itemset BETA - 1 to itemset ALPHA + 1
			for(int i = element.positionBetaItemset - 1; i > element.positionAlphaItemset; i--){
				// Get the itemset
				List<Integer> itemsetI = sequence.getItemsets().get(i);
				
				// Get the item
				for(int j=0; j < itemsetI.size(); j++){
					Integer itemJ = itemsetI.get(j);
				
					//Check if the item could be added to the left side, 
					// right side, or left and right side of the rule according to the lexicographical order
					boolean isLeft = itemJ > largestItemInAntecedent && itemJ < largestItemInConsequent;
					boolean isLeftRight = itemJ > largestItemInAntecedent && itemJ > largestItemInConsequent;
					boolean isRight = itemJ > largestItemInConsequent && itemJ < largestItemInAntecedent;
					
					// if the item can only be added to left side
					if(isLeft){
						// add the utility of that item to the "lutil"
						double profitItemJ = sequence.getUtilities().get(i).get(j);
						sumUtilityLeftUntilBetaPrime += profitItemJ;
						
					}else if(isRight){
						// use REUCP
						if(REUCM.get(largestItemInAntecedent).get(itemJ) == null) {
							continue;
						}
						// update RSU-table
						if(RSUTable.get(itemJ) == null) {
							RSUTable.put(itemJ, element.REEU);
						}else {
							RSUTable.put(itemJ, element.REEU + RSUTable.get(itemJ));
						}
						// use RERSUP
						if(RSUTable.get(itemJ) + table.REEU < minutil) {
							continue;
						}
						// if the item can only be added to right side
						// We will need to update the RE-table of the new rule
						// that could be generated with that item
						// Get the RE-table
						REtable tableItemJ = mapItemsTables.get(itemJ);
						if(tableItemJ == null){
							// if it does not exist, create a new RE-table
							tableItemJ = new REtable();
							mapItemsTables.put(itemJ, tableItemJ);
						}

						// Create a new element in the RE-table for that sequence
						ElementREtable newElement = new ElementREtable(element.numeroSequence);
 
						//  Add the utility of the item to the utility of the new rule
						double profitItemJ = sequence.getUtilities().get(i).get(j);
						newElement.utility = element.utility + profitItemJ;
					
						// Set the ULeft value for the new rule
						// which is the utility of the left side of the original rule minus
						// the utility of items that could be append to left side until the current itemset
						newElement.ULeft = element.ULeft - sumUtilityLeftUntilBetaPrime;
						
						// Set the ULeftRight value similarly
						newElement.ULeftRight = element.ULeftRight - sumULeftRightUntilBetaPrime;
	
						int sumUtilityRUtilItemsSmallerThanX = 0;
						int sumUtilityLRUtilItemsSmallerThanX = 0;
						
						// for each such itemset
						for(int z = i; z < element.positionBetaItemset; z++){
							List<Integer> itemsetZ = sequence.getItemsets().get(z);
							
							// for each item W
							for(int w=0; w < itemsetZ.size(); w++){
								Integer itemW = itemsetZ.get(w);
								
								// check if the item can be appended to the left or right side of the rule
								boolean wIsLeftRight = itemW > largestItemInAntecedent && itemW > largestItemInConsequent;
								// check if the item can only be appended to the right side of the rule
								boolean wIsRight = itemW > largestItemInConsequent && itemW < largestItemInAntecedent;
								
								// if the item can only be appended to the right side of the original rule
								// but is smaller than item W that is appended to the right side of the
								// new rule
								if(wIsRight && itemW < itemJ){
									// We will add its profit to the sum for RUtil
									double profitItemW = sequence.getUtilities().get(z).get(w);
									sumUtilityRUtilItemsSmallerThanX += profitItemW;
								}else if(wIsLeftRight && itemW > itemJ){
									// If it is an item that can be appended to the left or right side of
									// the original rule and is greater than the current item J
									// we will add it to the sum for LRUtil
									double profitItemW = sequence.getUtilities().get(z).get(w);
									sumUtilityLRUtilItemsSmallerThanX += profitItemW;
								}
							}
						}
						// Then we will update the URight for the new rule as follows:
						newElement.URight = element.URight - profitItemJ 
								+ sumUtilityLRUtilItemsSmallerThanX - sumUtilityRUtilItemsSmallerThanX;
	
						// We will update the position of Beta and alpha in the sequence
						newElement.positionBetaItemset = i; 
						newElement.positionAlphaItemset = element.positionAlphaItemset; 

						// calculate the REEU of the rule in this ElementREtable
						newElement.calculateREEU();
						
						// We have finished creating the element for that sequence for the new rule
						// so we will add it to the RE-table
						tableItemJ.addElement(newElement);
						
					}else if(isLeftRight){
						// use REUCP
						if(REUCM.get(largestItemInAntecedent).get(itemJ) == null) {
							sumULeftRightUntilBetaPrime += sequence.getUtilities().get(i).get(j);
							continue;
						}
						// update RSU-table
						if(RSUTable.get(itemJ) == null) {
							RSUTable.put(itemJ, element.REEU);
						}else {
							RSUTable.put(itemJ, element.REEU + RSUTable.get(itemJ));
						}
						// use RERSUP
						if(RSUTable.get(itemJ) + table.REEU < minutil) {
							sumULeftRightUntilBetaPrime += sequence.getUtilities().get(i).get(j);
							continue;
						}

						// Get the table
						REtable tableItemJ = mapItemsTables.get(itemJ);
						if(tableItemJ == null){
							// if it does not exist, create a new RE-table
							tableItemJ = new REtable();
							mapItemsTables.put(itemJ, tableItemJ);
						}

						// Create a new element in the table
						ElementREtable newElement = new ElementREtable(element.numeroSequence); 
 
						// Copy the utility of the original rule and add the utility of the item
						// in the current sequence.
						double profitItemJ = sequence.getUtilities().get(i).get(j);
						newElement.utility = element.utility + profitItemJ;
					
						// Set the ULeft value as the ULeft of the original rule
						// minus the utility of items until the beta prime itemset that could
						// be appended only on the left side of the rule
						newElement.ULeft = element.ULeft - sumUtilityLeftUntilBetaPrime;
						
						// Set the ULeftRight value as the ULeftRight of the original rule
						// minus the utility of items until the beta prime itemset that could
						// be appended  on the right or left side of the rule
						newElement.ULeftRight = element.ULeftRight - profitItemJ - sumULeftRightUntilBetaPrime;
						
						sumULeftRightUntilBetaPrime += profitItemJ;
						
						int sumUtilityRigthItemSmallerThanX = 0;
						
						// For each itemset 
						for(int z = i; z < element.positionBetaItemset; z++){
							List<Integer> itemsetZ = sequence.getItemsets().get(z);
							
							//for each item W in that itemset
							for(int w=0; w < itemsetZ.size(); w++){
								// If w is greater than J according to the lexicographical
								// order, we skip it because we are not interested here.
								Integer itemW = itemsetZ.get(w);
								if(itemW > itemJ){
									break;  
								}
								// Otherwise, we check if the item could be append on the right side
								// but not on the left side
								boolean wEstD = itemW > largestItemInConsequent && itemW < largestItemInAntecedent;
								
								// IF it is the case
								if(wEstD){
									// then we add the sum of the utility of item W in our
									// temporary variable
									double profitItemW = sequence.getUtilities().get(z).get(w);
									sumUtilityRigthItemSmallerThanX += profitItemW;
								}
							}
						}
						
						// After that we have the informatoin to update the URight value.
						// It is the URight of the original rule minus the content of the temporary
						// variable that we calculated above
						newElement.URight = element.URight - sumUtilityRigthItemSmallerThanX;
	
						// The first itemset of the right side of the rule has now changed.
						// We thus set beta to the new value "i"
						newElement.positionBetaItemset = i; 
						// The left side of the rule has not changed, so Alpha stay the same.
						newElement.positionAlphaItemset = element.positionAlphaItemset; 

						// calculate the REEU of the rule in this ElementREtable
						newElement.calculateREEU();
						
						// Finally, we add the element that we just created to the RE-table
						// of the new rule.
						tableItemJ.addElement(newElement);
					}
					
				}
			}
			
		}

		// destroy the RSU-table
		RSUTable = null;
		
		// For each new rule
		for(Entry<Integer, REtable> entryItemTable :  mapItemsTables.entrySet()){
			// We get the item and its RE-table
			Integer item = entryItemTable.getKey();
			REtable REtable = entryItemTable.getValue();
			
			// We check if we should try to expand its left side
			boolean shouldExpandLeftSide;
			// We check if we should try to expand its right side
			boolean shouldExpandRightSide;
					

			shouldExpandLeftSide = REtable.LEEU >= minutil && antecedent.length+1 < maxSizeAntecedent;
			shouldExpandRightSide = REtable.REEU >= minutil && consequent.length+1 < maxSizeConsequent;
			
					
			// check if the rule is high utility
			boolean isHighUtility = REtable.totalUtility >= minutil;
			
			// We create the consequent for the new rule by appending the new item
			int [] newConsequent= new int[consequent.length+1];
			System.arraycopy(consequent, 0, newConsequent, 0, consequent.length);
			newConsequent[consequent.length] = item;
			
			// We calculate the confidence
			double confidence =  (double) REtable.elements.size() / (double) sequenceIdsAntecedent.getSize();
			
			// If the rule is high utility and high confidence
			if(isHighUtility && confidence >= minConfidence){
				// We save the rule to file
				saveRule(antecedent, newConsequent, REtable.totalUtility, REtable.elements.size() , confidence);

			}

			// If we should try to expand the left side of this rule
			if(shouldExpandLeftSide){
				expandFirstLeft(REtable, antecedent, newConsequent, sequenceIdsAntecedent);
			}
			
			// If we should try to expand the right side of this rule
			if(shouldExpandRightSide){
				expandRight(REtable, antecedent, newConsequent, sequenceIdsAntecedent);
			}
		}
		
		// Check the maximum memory usage
		MemoryLogger.getInstance().checkMemory();
	}
	
	/**
	 * This method will recursively try to append items to the left side of a rule to generate
	 * rules containing one more item on the left side.  This method is only called for rules
	 * of size 1*1, thus containing two items (e.g. a -> b)
	 * @param REtable the rule RE-table
	 * @param antecedent the rule antecedent
	 * @param consequent the rule consequent
	 * @param sequenceIDsConsequent the list of sequences ids of sequences containing the rule antecedent
	 * @throws IOException if error while writting to file
	 */
	private void expandFirstLeft(REtable REtable, int[] antecedent,
		int[] consequent, ListSequenceIDs sequenceIDsConsequent) throws IOException {
		
		expandCount++;

		// We first find the largest item in the left side of the rule
		int largestItemInAntecedent = antecedent[antecedent.length -1];
		// the largest item in the right side of the rule
		int largestItemInConsequent = consequent[consequent.length -1];

		// We create a new map where we will build the LE-table for the new rules that
		// will be created by adding an item to the current rule.
		// Key: an item appended to the rule     Value: the LE-table of the corresponding new rule
		Map<Integer, LEtable> mapItemLEtable = new HashMap<Integer, LEtable>();
		
		// initialize the RSU-table
		Map<Integer, Double> RSUTable = new HashMap<Integer, Double>();
		
		// for each sequence containing the rule (a line in the RE-table of the original rule)
		for(ElementREtable element : REtable.elements){
			
			// update the LEEU (also is RRSU)
			REtable.LEEU -= element.LEEU;
			
			// if the ULeft is 0 for that rule in that sequence,
			// we do not need to scan this sequence.
			if(element.ULeft  == 0){
				continue;
			}
			
			// Get the sequence
			SequenceWithUtility sequence = database.getSequences().get(element.numeroSequence);

			// For each itemset before beta
			for(int i = 0; i < element.positionBetaItemset; i++){
				List<Integer> itemsetI = sequence.getItemsets().get(i);
				
				// For each item
				for(int j = 0; j < itemsetI.size(); j++){
					Integer itemJ = itemsetI.get(j);
				
					// Check if the item is greater than items in the antecedent of the rule 
					// according to the lexicographical order 
					if(itemJ <= largestItemInAntecedent){
						continue;
					}
					if(REUCM.get(itemJ).get(largestItemInConsequent) == null) {
						continue;
					}
					
					if(RSUTable.get(itemJ) == null) {
						RSUTable.put(itemJ, element.LEEU);
					}else {
						RSUTable.put(itemJ, element.LEEU + RSUTable.get(itemJ));
					}

					if(RSUTable.get(itemJ) + REtable.LEEU < minutil) {
						continue;
					}
					
					// Otherwise, we need to update the LE-table of the item
					// Get the LE-table of the item
					LEtable tableItemJ = mapItemLEtable.get(itemJ);
					if(tableItemJ == null){
						// if no LE-table, we create one
						tableItemJ = new LEtable();
						mapItemLEtable.put(itemJ, tableItemJ);
					}


					// We will add a new element in the RE-table
					ElementLEtable newElement = new ElementLEtable(element.numeroSequence);

					// we will update the utility vlaue of that rule by adding the utility of the item
					// in that sequence
					double profitItemJ = sequence.getUtilities().get(i).get(j);
					newElement.utility = element.utility + profitItemJ;

					newElement.ULeft = element.ULeft + element.ULeftRight - profitItemJ;

					// Then, we will scan itemsets from the first one until the beta -1  itemset 
					// in the sequence.
					// We will subtract the utility of items that are smaller than item J 
					// according to the lexicographical order from ULeft because they
					// cannot be added anymore to the new rule.

					// For each itemset before the beta itemset
					for(int z=0; z < element.positionBetaItemset; z++){
						List<Integer> itemsetZ = sequence.getItemsets().get(z);
						
						// For each item W in that itemset
						for(int w= itemsetZ.size()-1; w >= 0 ; w--){
							Integer itemW = itemsetZ.get(w);

							// if the item is smaller than the larger item in the left side of the rule
							if(itemW <= largestItemInAntecedent){
								// we break;
								break;  
							}
							
							// otherwise, if item W is smaller than item J
							if(itemJ > itemW){
								// We will subtract the utility of W from ULeft
								double profitItemW = sequence.getUtilities().get(z).get(w);
								newElement.ULeft -= profitItemW;
							}
						}
					}
					
					
					// calculate the LEEU of the rule in this ElementLEtable
					newElement.calculateLEEU();
					
					// Now that we have created the element for that sequence and that new rule
					// we will add the LE-table of that new rule
					tableItemJ.addElement(newElement);
				 
				}
			}
		}
		
		// After that for each new rule, we create a table to store the beta values 
		// for each sequence where the new rule appears.
		// The reason is that the "beta" column of any new rules that will be generated
		// by recursively adding to the left, will staty the same. So we don't store it in the
		// LEtable of the rule directly but in a separated structure.
		
		// Beta is a map where the key is a sequence id
		//   and the key is the position of an itemset in the sequence.
		Map<Integer, Integer> tableBeta = null;
		
	
		// For each new rule
		for(Entry<Integer, LEtable> entryItemTable :  mapItemLEtable.entrySet()){
			// We get the item that was added to create the new rule
			Integer item = entryItemTable.getKey();
			// We get the LE-table of the new rule
			LEtable tableItem = entryItemTable.getValue();
			
			// We check if we should try to expand its left side
			boolean shouldExpandLeftSide = tableItem.LEEU >= minutil && antecedent.length+1 < maxSizeAntecedent;
			
			// We need to calculate the list of sequences ids containing the antecedent of the new
			// rule since the antecedent has changed
			ListSequenceIDs sequenceIdentifiersNewAntecedent = null;

			// To calculate the confidence
			double confidence = 0;
			
			// If we should try to expand the left side of the rule
			// or if the rule is high utility, we recalculate the sequences ids containing
			// the antecedent
			if(shouldExpandLeftSide || tableItem.utility >= minutil ){
				// We obtain the list of sequence ids for the item
				ListSequenceIDs sequencesIdsItem = mapItemSequences.get(item);
						
				// We perform the intersection of the sequences ids of the antecedent
				// with those of the item to obtain the sequence ids of the new antecedent.
				sequenceIdentifiersNewAntecedent = sequenceIDsConsequent.intersection(sequencesIdsItem);
				 
				// we calculate the confidence
				confidence =  (double) tableItem.elements.size() / (double) sequenceIdentifiersNewAntecedent.getSize();
			}

			// if the new rule is high utility and has a high confidence
			boolean isHighUtilityAndHighConfidence = tableItem.utility >= minutil && confidence >= minConfidence;
			if(isHighUtilityAndHighConfidence ){

				// We create the antecedent for the new rule by appending the new item
				int [] nouvelAntecedent = new int[antecedent.length+1];
				System.arraycopy(antecedent, 0, nouvelAntecedent, 0, antecedent.length);
				nouvelAntecedent[antecedent.length] = item;

				// We save the rule to file
				saveRule(nouvelAntecedent, consequent, tableItem.utility, tableItem.elements.size(), confidence);

			}
			// If we should try to expand the left side of this rule
			if(shouldExpandLeftSide){
				// We create the antecedent for the new rule by appending the new item
				int [] newAntecedent = new int[antecedent.length+1];
				System.arraycopy(antecedent, 0, newAntecedent, 0, antecedent.length);
				newAntecedent[antecedent.length] = item;
				
				// We create the table for storing the beta position in each sequence
				if(tableBeta == null){
					tableBeta = new HashMap<Integer, Integer>();
					// We loop over each line from the original RE-table and copy the 
					// beta value for each line
					
					// For each element of the utility of the original rule
					for(ElementREtable element : REtable.elements){
						// copy the beta position
						tableBeta.put(element.numeroSequence, element.positionBetaItemset);
					}
				}
				
				// we recursively try to expand this rule
				expandSecondLeft(tableItem, newAntecedent, consequent, sequenceIdentifiersNewAntecedent, tableBeta);
	
			}
		}
		// We check the memory usage for statistics
		MemoryLogger.getInstance().checkMemory();
	}

	/**
	 * This method will recursively try to append items to the left side of a rule to generate
	 * rules containing one more item on the left side.  This method is called for rules
	 * containing at least 2 items on their left side already. For rules having 1 item on their left side
	 * another method is used instead.
	 * 
	 * @param LEtable the rule LE-table
	 * @param antecedent the rule antecedent
	 * @param consequent the rule consequent
	 * @param sequenceIDsConsequent the list of sequences ids of sequences containing the rule antecedent
	 * @throws IOException if error while writting to file
	 */
	private void expandSecondLeft(
			LEtable LEtable,
			int[] antecedent, int[] consequent,
			ListSequenceIDs sequenceIDsConsequent,
			Map<Integer, Integer> tableBeta) throws IOException {
		
		expandCount++;

		// We first find the largest item in the left side of the rule
		int largestItemInAntecedent = antecedent[antecedent.length -1];
		// the largest item in the right side of the rule
		int largestItemInConsequent = consequent[consequent.length -1];
		
		// We create a new map where we will build the LE-table for the new rules that
		// will be created by adding an item to the current rule.
		// Key: an item appended to the rule     Value: the LE-table of the corresponding new rule
		Map<Integer, LEtable> mapItemLEtable = new HashMap<Integer, LEtable>();

		Map<Integer, Double> RSUTable = new HashMap<Integer, Double>();
		
		// for each sequence containing the rule (a line in the RE-table of the original rule)
		for(ElementLEtable element : LEtable.elements){
			
			LEtable.LEEU -= element.LEEU;
			
			// if the ULeft is 0 for that rule in that sequence,
			// we do not need to scan this sequence.
			if(element.ULeft  == 0){
				continue;
			}

			// Get the sequence
			SequenceWithUtility sequence = database.getSequences().get(element.sequenceID);
			
			// Get the beta position in that sequence
			Integer positionBetaItemset = tableBeta.get(element.sequenceID);

			// For each itemset before beta
			for(int i=0; i < positionBetaItemset; i++){
				List<Integer> itemsetI = sequence.getItemsets().get(i);
				
				//for each  item
				for(int j=0; j < itemsetI.size(); j++){
					Integer itemJ = itemsetI.get(j);
				
					// Check if the item is greater than items in the antecedent of the rule 
					// according to the lexicographical order 
					if(itemJ <= largestItemInAntecedent){
						continue;
					}

					if(REUCM.get(itemJ).get(largestItemInConsequent) == null) {
						continue;
					}

					if(RSUTable.get(itemJ) == null) {
						RSUTable.put(itemJ, element.LEEU);
					}else {
						RSUTable.put(itemJ, element.LEEU + RSUTable.get(itemJ));
					}

					if(RSUTable.get(itemJ) + LEtable.LEEU < minutil) {
						continue;
					}
					
					LEtable tableItemJ = mapItemLEtable.get(itemJ);
					if(tableItemJ == null){
						// if no LE-table, we create one
						tableItemJ = new LEtable();
						mapItemLEtable.put(itemJ, tableItemJ);
					}

					// We will add a new element in the LE-table
					ElementLEtable newElement = new ElementLEtable(element.sequenceID);
	

					// we will update the utility vlaue of that rule by adding the utility of the item
					// in that sequence
					double utilityItemJ = sequence.getUtilities().get(i).get(j);
					newElement.utility = element.utility + utilityItemJ;
					
					// The ULeft value is updated by subtracting the utility of the item
					newElement.ULeft = element.ULeft - utilityItemJ;
					
					// for each itemset
					for(int z=0; z < positionBetaItemset; z++){
						List<Integer> itemsetZ = sequence.getItemsets().get(z);
						
						// for each item
						for(int w= itemsetZ.size()-1; w >= 0 ; w--){
							Integer itemW = itemsetZ.get(w);
							// if the item is smaller than the larger item in the left side of the rule
							if(itemW <= largestItemInAntecedent){
								break; 
							}
							// otherwise, if item W is smaller than item J
							if(itemW < itemJ){
								// We will subtract the utility of W from ULeft
								double utilityItemW = sequence.getUtilities().get(z).get(w);
								newElement.ULeft -= utilityItemW;
							}
						}
					}

					newElement.calculateLEEU();
					
					// Now that we have created the element for that sequence and that new rule
					// we will add that element to tthe LE-table of that new rule
					tableItemJ.addElement(newElement);
				
				}
			}
		}

		// For each new rule
		for(Entry<Integer, LEtable> entryItemTable :  mapItemLEtable.entrySet()){
			// We get the item that was added to create the new rule
			Integer item = entryItemTable.getKey();
			// We get the LE-table of the new rule
			LEtable tableItem = entryItemTable.getValue();
			
			// We check if we should try to expand its left side
			boolean shouldExpandLeft = tableItem.LEEU >= minutil && antecedent.length+1 < maxSizeAntecedent;
			
			
			// We check if the rule is high utility
			boolean isHighUtility = tableItem.utility >= minutil;
			
			double confidence = 0;
			
			// We need to calculate the list of sequences ids containing the antecedent of the new
			// rule since the antecedent has changed
			ListSequenceIDs sequenceIdentifiersNewAntecedent = null;
			
			// If we should try to expand the left side of the rule
			// or if the rule is high utility, we recalculate the sequences ids containing
			// the antecedent
			if(shouldExpandLeft || isHighUtility ){
				// We obtain the list of sequence ids for the item
				ListSequenceIDs numerosequencesItem = mapItemSequences.get(item);
				
				// We perform the intersection of the sequences ids of the antecedent
				// with those of the item to obtain the sequence ids of the new antecedent.
				sequenceIdentifiersNewAntecedent = sequenceIDsConsequent.intersection(numerosequencesItem);

				// we calculate the confidence
				confidence =  (double) tableItem.elements.size() / (double) sequenceIdentifiersNewAntecedent.getSize(); 
			}
			
			// if the new rule is high utility and has a high confidence
			if(isHighUtility && confidence >= minConfidence){
				
				// We create the antecedent for the new rule by appending the new item
				int [] newAntecedent = new int[antecedent.length+1];
				System.arraycopy(antecedent, 0, newAntecedent, 0, antecedent.length);
				newAntecedent[antecedent.length] = item;

				// We save the rule to file
				saveRule(newAntecedent, consequent, tableItem.utility, tableItem.elements.size() , confidence);
			}
			
			// If we should try to expand the left side of this rule
			if(shouldExpandLeft){
				// We create the antecedent for the new rule by appending the new item
				int [] nouvelAntecedent = new int[antecedent.length+1];
				System.arraycopy(antecedent, 0, nouvelAntecedent, 0, antecedent.length);
				nouvelAntecedent[antecedent.length] = item;
	
				// we recursively call this method
				expandSecondLeft(tableItem, nouvelAntecedent, consequent, sequenceIdentifiersNewAntecedent, tableBeta);
			}
		}
		// We check the memory usage
		MemoryLogger.getInstance().checkMemory();
	}


	/**
	 * Print statistics about the last algorithm execution to System.out.
	 */
	public void printStats() {
		System.out.println("==============================================================================");
		System.out.println("---- US-Rule algorithm for high utility sequential rule mining ----");
		System.out.println("==============================================================================");
		System.out.println("\tminutil: " + minutil);
		System.out.println("\tSequential rules count: " + ruleCount);
		System.out.println("\tTotal time: " + (double)(timeEnd - timeStart) / 1000 + " s");
		System.out.println("\tMax memory (mb): "
				+ MemoryLogger.getInstance().getMaxMemory());
		System.out.println("\tExpand count: " + expandCount);
		System.out.println("==============================================================================");
	}
	

	/**
	 * This interface represents a list of sequences ids
	 */
	public interface ListSequenceIDs {
		/**
		 * This method adds a sequence id to this list
		 * @param int the sequence id
		 */
		public abstract void addSequenceID(int noSequence);

		/**
		 * Get the number of sequence ids
		 * @return the number of sequence ids
		 */
		public abstract int getSize();

		/**
		 *  Method to intersect two lists of sequences ids
		 * @param vector another list
		 * @return the intersection of this list and the other list.
		 */
		public abstract ListSequenceIDs intersection(ListSequenceIDs vector2);
	}
	
	/**
	 * This class represents a list of sequences ids implemented by a bit vector
	 */
	public class ListSequenceIDsBitVector implements ListSequenceIDs{
		// the internal bitset
		private BitSet bitset = new BitSet();
		// the number of bit set to 1 in the bitset
		private int size = -1;
		
		/**
		 * Constructor
		 */
		public ListSequenceIDsBitVector(){
		}

		@Override
		/**
		 * This method adds a sequence id to this list
		 * @param int the sequence id
		 */
		public void addSequenceID(int bit){
			bitset.set(bit);
		}
		
		/**
		 * Get the number of sequence ids
		 * @return the number of sequence ids
		 */
		public int getSize(){
			// if we don't know the size
			if(size == -1){
				// we calculate it but remember it in variable "size" for future use.
				size = bitset.cardinality();
			}
			// return the size
			return size;
		}
		
		/**
		 *  Method to intersect two lists of sequences ids
		 * @param vector another list
		 * @return the intersection of this list and the other list.
		 */
		public ListSequenceIDs intersection(ListSequenceIDs vector2){
			//  we get the first vector
			ListSequenceIDsBitVector bitVector2 = (ListSequenceIDsBitVector) vector2;
			
			// we create a new vector for the result
			ListSequenceIDsBitVector result = new ListSequenceIDsBitVector();
			// we clone the first bit vecotr
			result.bitset = (BitSet) bitset.clone();
			// we intersect both bit vector
			result.bitset.and(bitVector2.bitset);
			// Return the result
			return result;
		}
		
		/**
		 * Get a string representation of this list
		 * @return a string
		 */
		public String toString() {
			return bitset.toString();
		}
	}
	

	/**
	 * This class represents a list of sequences ids implemented by an array list
	 */
	public class ListSequenceIDsArrayList implements ListSequenceIDs{
		// the internal array list representation
		List<Integer> list = new ArrayList<Integer>();
		
		/**
		 * Constructor
		 */
		public ListSequenceIDsArrayList(){
		}

		/**
		 * This method adds a sequence id to this list
		 * @param int the sequence id
		 */
		public void addSequenceID(int noSequence){
			list.add(noSequence);
		}
		

		/**
		 * Get the number of sequence ids
		 * @return the number of sequence ids
		 */
		public int getSize(){
			return list.size();
		}
		
		/**
		 *  Method to intersect two lists of sequences ids
		 * @param vector another list
		 * @return the intersection of this list and the other list.
		 */
		public ListSequenceIDs intersection(ListSequenceIDs list2){
			// Get the second list
			ListSequenceIDsArrayList arrayList2 = (ListSequenceIDsArrayList) list2;
			// Create a new list for the result
			ListSequenceIDs result = new ListSequenceIDsArrayList();
			
			// for each sequence id in this list
			for(Integer no : list){
				// if it appear in the second list
				boolean appearInSecondList = Collections.binarySearch(arrayList2.list, no) >= 0;
				if(appearInSecondList){
					// then we add it to the new list
					result.addSequenceID(no);
				}
			}
			// return the result
			return result;
		}
		
		/**
		 * Get a string representation of this list
		 * @return a string
		 */
		public String toString() {
			return list.toString();
		}
	}

	
	/**
	 * This class represents a LE-table used for left expansions
	 */
	public class LEtable{
		// the list of elements (lines) in that RE-table
		List<ElementLEtable> elements = new ArrayList<ElementLEtable>();
		// the total utility in that table
		int utility = 0;
		// the toal LEEU values of elements in that table
		double LEEU = 0;
		
		/**
		 * Constructor
		 */
		public LEtable(){
		}
		
		/**
		 * Add a new element to that table
		 * @param element the new element
		 */
		public void addElement(ElementLEtable element){
			// add the element
			elements.add(element);
			// add the utility of this element to the total utility of that table
			utility += element.utility;
			// add the LEEU of this element to the total for that table
			LEEU += element.LEEU;
		}
	}
	
	/**
	 * This class represents an element of a LE-table used for left expansions
	 */
	public class ElementLEtable{
		// the corresponding sequence id
		int sequenceID;
		// the utility
		double utility;
		// ULeft and LEEU
		double ULeft;
		double LEEU;
		
		/**
		 * Constructor
		 * @param sequenceID the sequence id
		 */
		public ElementLEtable(int sequenceID){
			this.sequenceID = sequenceID;
			this.utility = 0;
			this.ULeft = 0;
			this.LEEU = 0;
		}
		
		/**
		 * Constructor
		 * @param sequenceID a sequence id
		 * @param utility the utility
		 * @param uLeft the ULeft value
		 */
		public ElementLEtable(int sequenceID, int utility, int uLeft){
			this.sequenceID = sequenceID;
			this.utility = utility;
			this.ULeft = uLeft;
			this.LEEU = 0;
		}
		
		/**
		 * Calculate the LEEU of this sequence
		 */
		public void calculateLEEU() {
			if(this.ULeft != 0) {
				LEEU = (this.utility + this.ULeft);
			}
		}
	}
	
	/**
	 * This class represents a RE-table used for left or right expansions
	 */
	public class REtable{
		// the list of elements in that RE-table
		List<ElementREtable> elements = new ArrayList<ElementREtable>();
		// the total utility in that table
		double totalUtility = 0;
		
		// LEEU and REEU
		double LEEU = 0;
		double REEU = 0;
		
		/**
		 * Constructor
		 */
		public REtable(){
			
		}
		
		/**
		 * Add a new element to that table
		 * @param element the new element
		 */
		public void addElement(ElementREtable element){
			// add the element
			elements.add(element);
			// make the sum of the utility, LEEU, and REEU values
			totalUtility += element.utility;
			LEEU += element.LEEU;
			REEU += element.REEU;
		}
	}
	
	/**
	 * This class represents an element of a RE-table used for left or right expansions
	 */
	public class ElementREtable{
		// the corresponding sequence id
		int numeroSequence;
		// the utility
		double utility;
		// the ULeft value
		double ULeft;
		// the ULeftRight value
		double ULeftRight;
		// the URight value
		double URight;
		// LEEU and REEU
		double LEEU;
		double REEU;
		// Position (the alpha and beta values)
		int positionAlphaItemset = -1;
		int positionBetaItemset = -1;
		
		/**
		 * Constructor
		 * @param sequenceID the sequence id
		 */
		public ElementREtable(int sequenceID){
			this.numeroSequence = sequenceID;
			this.utility = 0;
			this.ULeft = 0;
			this.ULeftRight = 0;
			this.URight = 0;
			this.LEEU = 0;
			this.REEU = 0;
		}
		
		/**
		 * Constructor
		 * @param sequenceID a sequence id
		 * @param utility the utility
		 * @param uLeft the ULeft value
		 * @param uLeftRight the ULeftRight value
		 * @param uRight the URight value
		 */
		public ElementREtable(int sequenceID,
				double utility,
				double uLeft,
				double uLeftRight,
				double uRight){
			this.numeroSequence = sequenceID;
			this.utility = utility;
			this.ULeft = uLeft;
			this.ULeftRight = uLeftRight;
			this.URight = uRight;	
			this.LEEU = 0;
			this.REEU = 0;
		}
		
		
		public void calculateREEU() {
			if(ULeftRight != 0) {
				LEEU = utility + ULeftRight + ULeft;
				REEU = utility + ULeftRight + ULeft + URight;
			}else {
				if(ULeft != 0) {
					LEEU = utility + ULeft;
				}
				if(URight != 0) {
					REEU = utility + URight + ULeft;
				}
			}
		} 
	}
}
