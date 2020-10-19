package org.semanticweb.rulewerk.asp.model;

/*
 * #%L
 * Rulewerk Core Components
 * %%
 * Copyright (C) 2018 - 2020 Rulewerk Developers
 * %%
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 * #L%
 */

import org.semanticweb.rulewerk.core.reasoner.Algorithm;
import org.semanticweb.rulewerk.core.reasoner.KnowledgeBase;
import org.semanticweb.rulewerk.core.reasoner.Reasoner;

import java.io.IOException;

/**
 * Interface that extends the standard reasoner by ASP specific features
 */
public interface AspReasoner extends Reasoner {

	/**
	 * Getter for the transformed knowledge base that is an over-approximation of the ASP knowledge base.
	 *
	 * @return knowledge base
	 */
	KnowledgeBase getDatalogKnowledgeBase();

	/**
	 * Performs materialisation on the reasoner with the over-approximated {@link KnowledgeBase}, depending on the set
	 * {@link Algorithm}, and performs cautious reasoning for the {@link KnowledgeBase} representing an ASP program.
	 * To avoid non-termination, a reasoning timeout can be set ({@link Reasoner#setReasoningTimeout(Integer)}). <br>
	 *
	 * @return
	 *         <ul>
	 *         <li>{@code true}, if materialisation reached completion.</li>
	 *         <li>{@code false}, if materialisation has been interrupted before
	 *         completion.</li>
	 *         </ul>
	 * @throws IOException if I/O exceptions occur during reasoning.
	 */
	boolean reason() throws IOException;

	/**
	 * Gets the answer sets for the underlying knowledge base.
	 *
	 * @return an iterator of {@link AnswerSet}s
	 * @throws IOException an IO exception
	 */
	AnswerSetIterator getAnswerSets() throws IOException;

	/**
	 * Gets the answer sets for the underlying knowledge base. The result is limited to a given maximum, but might
	 * might contain fewer answer sets. If maximum is 0, all answer sets are returned.
	 *
	 * @param maximum an limit on the returned answer sets
	 * @return an iterator of {@link AnswerSet}s
	 * @throws IOException an IO exception
	 */
	AnswerSetIterator getAnswerSets(int maximum) throws IOException;
}