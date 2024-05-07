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

import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.Map;
import java.util.Set;
import java.util.function.Consumer;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

class PrunedProof<I extends AxiomPinpointingInference<?, ?>>
		extends DelegatingProof<I, Proof<? extends I>>
		implements Proof<I>, Consumer<I> {
	
	private static final Logger LOGGER_ = LoggerFactory
			.getLogger(PrunedProof.class);

	private final Map<Object, I> essentialInferences_ = new HashMap<Object, I>();

	public PrunedProof(Proof<? extends I> delegate, Object goal) {
		super(delegate);
		Set<Object> essential = Proofs.getEssentialAxioms(delegate, goal);
		LOGGER_.trace("Essential axioms: " + essential);
		Proofs.expand(essential,
				Proofs.filter(delegate,
						inf -> essential.containsAll(inf.getJustification())),
				goal, this);
	}

	@Override
	public void accept(I inf) {
		LOGGER_.trace("Essential inference: " + inf);
		essentialInferences_.put(inf.getConclusion(), inf);
	}

	@Override
	public Collection<? extends I> getInferences(Object conclusion) {
		I inf = essentialInferences_.get(conclusion);
		if (inf == null) {
			return super.getInferences(conclusion);
		}
		// else
		return Collections.singleton(inf);
	}

}
