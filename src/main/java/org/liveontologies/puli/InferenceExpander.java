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

import java.util.ArrayDeque;
import java.util.List;
import java.util.Queue;
import java.util.Set;
import java.util.function.Consumer;
import java.util.function.Predicate;

import com.google.common.collect.ArrayListMultimap;
import com.google.common.collect.ListMultimap;

class InferenceExpander<C, I extends Inference<? extends C>>
		implements Predicate<I> {

	private final Set<C> derivable_;

	private final Proof<? extends I> proof_;

	private final ListMultimap<C, I> watchInferences_ = ArrayListMultimap
			.create();
	private final ListMultimap<C, Integer> watchPositions_ = ArrayListMultimap
			.create();

	private final Queue<C> newlyDerived_ = new ArrayDeque<C>();

	private final Consumer<? super I> applied_;

	InferenceExpander(Set<C> derivable, Proof<? extends I> proof, C goal,
			Consumer<? super I> applied) {
		this.proof_ = proof;
		this.derivable_ = derivable;
		this.applied_ = applied;
		process(goal);
	}

	public static <C, I extends Inference<? extends C>> void expand(
			Set<C> derivable, Proof<? extends I> proof, C goal,
			Consumer<? super I> applied) {
		new InferenceExpander<C, I>(derivable, proof, goal, applied);
	}

	void process(C goal) {
		Proofs.unfoldRecursively(proof_, goal, this);
	}

	@Override
	public boolean test(I inf) {
		List<? extends C> premises = inf.getPremises();
		for (int i = 0; i < premises.size(); i++) {
			C premise = premises.get(i);
			if (!derivable_.contains(premise)) {
				watchInferences_.put(premise, inf);
				watchPositions_.put(premise, i);
				return true;
			}
		}
		// all premises are derived
		C conclusion = inf.getConclusion();
		if (derivable_.add(conclusion)) {
			applied_.accept(inf);
			newlyDerived_.add(conclusion);
			propagate();
		}
		return true;
	}

	void propagate() {
		for (;;) {
			C next = newlyDerived_.poll();
			if (next == null) {
				return;
			}
			List<I> watch = watchInferences_.removeAll(next);
			List<Integer> positions = watchPositions_.removeAll(next);
			for (int i = 0; i < watch.size(); i++) {
				I inf = watch.get(i);
				int pos = positions.get(i);
				List<? extends C> premises = inf.getPremises();
				for (;;) {
					pos++;
					if (pos == premises.size()) {
						// all premises are derived
						C conclusion = inf.getConclusion();
						if (derivable_.add(conclusion)) {
							applied_.accept(inf);
							newlyDerived_.add(conclusion);
						}
						break;
					}
					// else
					C premise = premises.get(pos);
					if (derivable_.contains(premise)) {
						continue;
					}
					// else
					watchInferences_.put(premise, inf);
					watchPositions_.put(premise, pos);
					break;
				}
			}
		}

	}

}
