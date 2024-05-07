/*-
 * #%L
 * Proof Utility Library
 * $Id:$
 * $HeadURL:$
 * %%
 * Copyright (C) 2014 - 2017 Live Ontologies Project
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
package org.liveontologies.puli;

/**
 * Testing derivability of conclusions using inferences. A conclusion is
 * derivable either if it is a conclusion of an inference with zero premises or
 * a conclusion of an inference all of which premises are derivable.
 * 
 * @author Yevgeny Kazakov
 *
 * @param <I>
 *            the type of inferences
 */
public interface DerivabilityChecker<I extends Inference<?>> {

	/**
	 * @return the {@link Proof} in which derivability is checked
	 */
	public Proof<? extends I> getProof();

	/**
	 * Checks if a given conclusion is derivable
	 * 
	 * @param conclusion
	 *            the conclusion to be tested for derivability
	 * @return {@code true} if conclusion is derivable and {@code false}
	 *         otherwise
	 */
	public boolean isDerivable(Object conclusion);

	/**
	 * Returns an acyclic {@link Proof} that can explain why the given
	 * conclusion is derivable or not.
	 * 
	 * A {@link Proof} is acyclic if all conclusions can be totally ordered such
	 * that for each inference returned by {@link Proof#getInferences(Object)}),
	 * the conclusion of the inference obtained by
	 * {@link Inference#getConclusion()} is larger in this ordering than all
	 * premises of the inference obtained by {@link Inference#getPremises()}.
	 * 
	 * If the given conclusion is derivable, i.e., {@link #isDerivable(Object)}
	 * returns {@code true}, the returned {@link Proof} can be used to retrieve
	 * the inferences using which this conclusion can be derived. Specifically,
	 * {@link Proof#getInferences(Object)} should return a nonempty set of
	 * inferences for this conclusion, and likewise for every premise of these
	 * inferences. Since the returned {@link Proof} is acyclic, eventually all
	 * returned inferences will have no premises.
	 * 
	 * If the given conclusion is not derivable, i.e.,
	 * {@link #isDerivable(Object)} returns {@code false}), then the returned
	 * {@link Proof} can be used to test which conclusions cannot be derived: if
	 * {@link Proof#getInferences(Object)} returns the empty set for some
	 * conclusion then for every inference of this conclusion in the original
	 * {@link #getProof()}, there exists a premise which likewise cannot be
	 * derived, i.e., {@link Proof#getInferences(Object)} for this premise,
	 * likewise, returns the empty set. (Note that this, in particular, means
	 * that every inference of a non-derivable conclusion contains at least one
	 * premise.)
	 * 
	 * All inferences returned by the resulting {@link Proof} using
	 * {@link Proof#getInferences(Object)} must be subsets of inferences
	 * returned by {@link #getProof()}.
	 * 
	 * @param conclusion
	 * @return the proof consisting of only derivable conclusions
	 * 
	 * @see Proofs#checkAcyclicity(Proof, Object, java.util.function.Consumer)
	 */
	public Proof<I> explainIsDerivable(Object conclusion);

}
