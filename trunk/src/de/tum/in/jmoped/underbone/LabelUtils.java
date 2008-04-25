package de.tum.in.jmoped.underbone;

import java.util.ArrayList;
import java.util.List;


/**
 * A utility class for reasoning about Remopla labels.
 * 
 * @author suwimont
 *
 */
public class LabelUtils {

	/**
	 * Extracts the method descriptor from the label. 
	 * 
	 * @param label the label.
	 * @return the method descriptor.
	 */
	static String extractMethodDescriptorFromLabel(String label) {
		return label.substring(label.indexOf("("), LabelUtils.getOffsetPosition(label));
	}
	
	/**
	 * Trims the ending digits.
	 * 
	 * @param label the Remopla label
	 * @return the trimmed label.
	 */
	public static String trimOffset(String label) {	
		return label.substring(0, LabelUtils.getOffsetPosition(label));
	}
	
	/**
	 * Extracts the offset number at the end of the label string.
	 * 
	 * @param label
	 * @return o if there is no number
	 */
	public static int getOffset(String label)
	{
		int offset = LabelUtils.getOffsetPosition(label);
		if (offset >= 0) {
			int to = label.lastIndexOf(SUFFIX_SEPARATOR);
			if (to == -1) to = label.length();
			return Integer.parseInt(label.substring(offset, to));
		}
		return 0;
	}

	/**
	 * Returns the position of the first digit of the offset number.
	 * 
	 * @return -1 if there is none
	 */
	public static int getOffsetPosition(String label) {
		
		int offset = label.length() - 1;
		
		// Bypasses non-digit suffix
		while (offset >= 0 && !Character.isDigit(label.charAt(offset)))
			offset--;
		
		// Goes through the digits
		while (offset >= 0 && Character.isDigit(label.charAt(offset)))
			offset--;
		
		// At least one digit
		if (offset < label.length() - 1)
			return offset + 1;
			
		return -1;
	}

	/**
	 * Returns the list of parameter types as specified by the 
	 * <code>descriptor</code>.
	 * 
	 * @param descriptor the method descriptor.
	 * @return the list of parameter types.
	 */
	public static List<String> getParamTypes(String descriptor) {
		
		String param = descriptor.substring(1, descriptor.indexOf(")"));
		StringBuilder tmp;
		
		List<String> paramList = new ArrayList<String>();
		for (int i = 0; i < param.length(); i++) {
			switch (param.charAt(i)) {		
				case '[': 
					tmp = new StringBuilder();
					while (param.charAt(i) == '[') {
						tmp.append("[");
						i++;
					}
					if (param.charAt(i) == 'L') {
						while (param.charAt(i) != ';') {
							tmp.append(param.charAt(i));
							i++;
						}
						tmp.append(";");
					} else {
						tmp.append(param.charAt(i));
					}
					paramList.add(tmp.toString());
					break;
					
				case 'L':
				case 'Q':
					tmp = new StringBuilder();
					while (param.charAt(i) != ';') {
						tmp.append(param.charAt(i));
						i++;
					}
					tmp.append(";");
					paramList.add(tmp.toString());
					break;
					
				default:
					paramList.add(new String(new char[] {param.charAt(i)}));
			}
		}
		
		return paramList;
	}

	private static final String SUFFIX_SEPARATOR = "#";
	private static final String ASSERTION_ERROR = "AssertionError";
	private static final String HO_ERROR = "HO";
	private static final String NPE_ERROR = "NPE";
	private static final String IOOB_ERROR = "IOOB";
	
	/**
	 * Creates a new label by suffixing the <code>label</code>.
	 * The new label indicates an assertion error at the <code>label</code>. 
	 * 
	 * @param label the label.
	 * @return the assertion error label.
	 */
	public static String formatAssertionName(String label) {
		return label + SUFFIX_SEPARATOR + ASSERTION_ERROR;
	}
	
	/**
	 * Returns <code>true</code> if the <code>label</code> is an assertion name.
	 * 
	 * @param label the label.
	 * @return <code>true</code> if the <code>label</code> is an assertion name.
	 */
	public static boolean isAssertionName(String label) {
		return label.endsWith(ASSERTION_ERROR);
	}
	
	/**
	 * Creates a new label by suffixing the <code>label</code>.
	 * The new label indicates a heap overflow at the <code>label</code>. 
	 * 
	 * @param label the label.
	 * @return the assertion error label.
	 */
	public static String formatHeapOverflowName(String label) {
		return label + SUFFIX_SEPARATOR + HO_ERROR;
	}
	
	/**
	 * Returns <code>true</code> if the <code>label</code> is a heap-overflow name.
	 * 
	 * @param label the label.
	 * @return <code>true</code> if the <code>label</code> is a heap-overflow name.
	 */
	public static boolean isHeapOverflowName(String label) {
		return label.endsWith(HO_ERROR);
	}
	
	/**
	 * Creates a new label by suffixing the <code>label</code>.
	 * The new label indicates a NullPointerException at the <code>label</code>. 
	 * 
	 * @param label the label.
	 * @return the assertion error label.
	 */
	public static String formatNpeName(String label) {
		return label + SUFFIX_SEPARATOR + NPE_ERROR;
	}
	
	/**
	 * Returns <code>true</code> if the <code>label</code> is a NullPointerException name.
	 * 
	 * @param label the label.
	 * @return <code>true</code> if the <code>label</code> is a NullPointerException name.
	 */
	public static boolean isNpeName(String label) {
		return label.endsWith(NPE_ERROR);
	}
	
	/**
	 * Creates a new label by suffixing the <code>label</code>.
	 * The new label indicates a ArrayIndexOutOfBoundsException at the <code>label</code>. 
	 * 
	 * @param label the label.
	 * @return the assertion error label.
	 */
	public static String formatIoobName(String label) {
		return label + SUFFIX_SEPARATOR + IOOB_ERROR;
	}
	
	/**
	 * Returns <code>true</code> if the <code>label</code> is a ArrayIndexOutOfBoundsException name.
	 * 
	 * @param label the label.
	 * @return <code>true</code> if the <code>label</code> is a ArrayIndexOutOfBoundsException name.
	 */
	public static boolean isIoobName(String label) {
		return label.endsWith(IOOB_ERROR);
	}
	
	public static String trimSuffix(String label) {
		
		return label.substring(0, label.lastIndexOf(SUFFIX_SEPARATOR));
	}
	
	private static final String THREADSAVE = "save";
	
	public static String formatSave(int i) {
		return THREADSAVE + i;
	}
	
	private static final String WAITFLAG = "waitflag";
	
	public static String formatWaitFlag(int i) {
		return WAITFLAG + i;
	}
	
	private static final String WAITFOR = "waitfor";
	
	public static String formatWaitFor(int i) {
		return WAITFOR + i;
	}
}
