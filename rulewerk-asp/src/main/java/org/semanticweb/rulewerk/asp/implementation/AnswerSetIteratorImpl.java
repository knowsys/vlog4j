package org.semanticweb.rulewerk.asp.implementation;

import org.apache.commons.lang3.Validate;
import org.semanticweb.rulewerk.asp.model.AnswerSet;
import org.semanticweb.rulewerk.asp.model.AnswerSetIterator;
import org.semanticweb.rulewerk.asp.model.AspReasoningState;
import org.semanticweb.rulewerk.core.model.api.Literal;

import java.io.BufferedReader;
import java.io.IOException;
import java.util.*;

public class AnswerSetIteratorImpl implements AnswerSetIterator {

	Iterator<String> answerSetStringIterator;
	AspReasoningState reasoningState;
	Map<Integer, Literal> integerLiteralMap;

	/**
	 * Static function to create an answer set iterator that represents an erroneous computation.
	 * @return an answer set iterator
	 */
	public static AnswerSetIterator getErrorAnswerSetIterator() {
		return new AnswerSetIteratorImpl();
	}

	/**
	 * The constructor.
	 *
	 * @param reader the reader containing the answer sets
	 * @param integerLiteralMap map of integers to the literals they represent
	 * @throws IOException an IO exception
	 */
	public AnswerSetIteratorImpl(BufferedReader reader, Map<Integer, Literal> integerLiteralMap) throws IOException {
		Validate.notNull(reader);
		Validate.notNull(integerLiteralMap);

		String line;
		List<String> answerSetStrings = new ArrayList<>();
		while ((line = reader.readLine()) != null) {
			line = line.trim();
			if (line.startsWith("SATISFIABLE")) {
				reasoningState = AspReasoningState.SATISFIABLE;
			} else if (line.startsWith("UNSATISFIABLE")) {
				reasoningState = AspReasoningState.UNSATISFIABLE;
			} else if (line.startsWith("INTERRUPTED")) {
				reasoningState = AspReasoningState.INTERRUPTED;
			} else if (line.startsWith("Answer: ")) {
				answerSetStrings.add(reader.readLine());
			}
		}
		answerSetStringIterator = answerSetStrings.iterator();
		this.integerLiteralMap = integerLiteralMap;
	}

	/**
	 * Private constructor for an answer set iterator representing an erroneous result.
	 */
	private AnswerSetIteratorImpl() {
		answerSetStringIterator = Collections.emptyIterator();
		reasoningState = AspReasoningState.ERROR;
		integerLiteralMap = null;
	}

	@Override
	public boolean hasNext() {
		return answerSetStringIterator.hasNext();
	}

	@Override
	public AnswerSet next() {
		return new AnswerSetImpl(answerSetStringIterator.next(), integerLiteralMap);
	}

	@Override
	public AspReasoningState getReasoningState() {
		return reasoningState;
	}
}