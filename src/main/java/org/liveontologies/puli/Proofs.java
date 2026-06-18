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

import java.io.IOException;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.Deque;
import java.util.HashSet;
import java.util.List;
import java.util.Queue;
import java.util.Set;
import java.util.function.Consumer;
import java.util.function.Predicate;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import com.google.common.base.Function;
import com.google.common.collect.Collections2;
import com.google.common.collect.Sets;

/**
 * A collection of static methods for working with {@link Proof}s
 * 
 * @author Yevgeny Kazakov
 *
 */
public class Proofs {

	@SuppressWarnings("rawtypes")
	public static DynamicProof EMPTY_PROOF = new EmptyProof();

	/**
	 * @return a {@link DynamicProof} that has no inference, i.e.,
	 *         {@link DynamicProof#getInferences(Object)} is always the empty
	 *         set. This proof never changes so if a
	 *         {@link DynamicProof.ChangeListener} is added, it does not receive
	 *         any notifications.
	 */
	@SuppressWarnings("unchecked")
	public static <I extends Inference<?>> DynamicProof<I> emptyProof() {
		return (DynamicProof<I>) EMPTY_PROOF;
	}

	/**
	 * @param proof
	 * @param conclusion
	 * @return {@code true} if the given conclusion is derivable in the given
	 *         {@link Proof}, i.e., there exists an sequence of conclusions
	 *         ending with the given conclusion, such that for each conclusion
	 *         there exists an inference in {@link Proof#getInferences} that has
	 *         as premises only conclusions that appear before in this sequence.
	 */
	public static boolean isDerivable(Proof<?> proof, Object conclusion) {
		return getDerivabilityChecker(proof).isDerivable(conclusion);
	}

	public static DerivabilityChecker<?> getDerivabilityChecker(
			Proof<?> proof) {
		return new DerivabilityCheckerUP<>(
				transform(proof, inf -> justifyByEmpty(inf)));
	}

	public static boolean isDerivableFrom(Proof<? extends Object> proof,
			Object conclusion, Set<?> assertedConclusions) {
		return ProofNodes.isDerivable(ProofNodes.addAssertedInferences(
				ProofNodes.create(proof, conclusion), assertedConclusions));
	}

	public static <C> Proof<AssertedConclusionInference<C>> create(
			Stream<? extends C> asserted) {
		ModifiableProof<AssertedConclusionInference<C>> proof = new BaseProof<>();
		asserted.map(AssertedConclusionInference<C>::new)
				.forEach(proof::produce);
		return proof;
	}

	/**
	 * @param proofs
	 * @return the union of the given the {@link Proof}s, i.e., a {@link Proof}
	 *         that for each conclusion returns the union of inferences returned
	 *         by the proofs in the argument
	 */
	public static <I extends Inference<?>> Proof<I> union(
			final Iterable<? extends Proof<? extends I>> proofs) {
		return new ProofUnion<I>(proofs);
	}

	/**
	 * @param proofs
	 * @return the union of the given the {@link Proof}s, i.e., a {@link Proof}
	 *         that for each conclusion returns the union of inferences returned
	 *         by the proofs in the argument
	 */
	@SafeVarargs
	public static <I extends Inference<?>> Proof<I> union(
			final Proof<? extends I>... proofs) {
		return new ProofUnion<I>(proofs);
	}

	/**
	 * @param proof
	 * @return the {@link Proof} that has all inferences of the given
	 *         {@link Proof} except for inferences with non-empty justification.
	 * @see AxiomPinpointingInference#getJustification()
	 */
	public static <I extends AxiomPinpointingInference<?, ?>> Proof<I> filterJustifiedInferences(
			final Proof<? extends I> proof) {
		return filter(proof, inf -> inf.getJustification().isEmpty());
	}

	/**
	 * @param proof
	 * @param filter
	 *            a predicate determining if the inference should be kept in the
	 *            resulting proof
	 * @return the {@link Proof} that has all inferences of the given
	 *         {@link Proof} except for inferences for which the predicate
	 *         returns false
	 */
	public static <I extends Inference<?>> Proof<I> filter(
			final Proof<? extends I> proof, final Predicate<? super I> filter) {
		return new Proof<I>() {

			@Override
			public Collection<? extends I> getInferences(Object conclusion) {
				return proof.getInferences(conclusion).stream().filter(filter)
						.collect(Collectors.toList());
			}

		};
	}

	public static <I extends Inference<?>, J extends Inference<?>> Proof<J> transform(
			final Proof<I> proof, Function<? super I, J> transformatin) {
		return new Proof<J>() {

			@Override
			public Collection<J> getInferences(Object conclusion) {
				return Collections2.transform(proof.getInferences(conclusion),
						transformatin);
			}
		};
	}

	public static <A, I extends AxiomPinpointingInference<?, ? extends A>> Proof<I> filterJustified(
			Proof<? extends I> proof, Predicate<? super A> include) {
		return Proofs.filter(proof,
				inf -> inf.getJustification().stream().allMatch(include));
	}

	static <C> AxiomPinpointingInference<C, C> justifyByConclusion(
			Inference<? extends C> inf) {
		return new AxiomPinpointingInferenceAdapter<C, C>(inf) {
			@Override
			public Set<? extends C> getJustification() {
				return Collections.singleton(inf.getConclusion());
			};
		};
	}

	public static <C, A> AxiomPinpointingInference<C, A> justifyByEmpty(
			Inference<? extends C> inf) {
		return new AxiomPinpointingInferenceAdapter<C, A>(inf) {
			@Override
			public Set<? extends A> getJustification() {
				return Collections.emptySet();
			};
		};
	}

	public static <C> AxiomPinpointingInference<C, C> justifyAsserted(
			Inference<? extends C> inf) {
		return new AssertedAxiomPinpointingInferenceAdapter<>(inf);
	}

	public static <C> Proof<AxiomPinpointingInference<C, C>> justifyAsserted(
			Proof<? extends Inference<? extends C>> proof) {
		return transform(proof, Proofs::justifyAsserted);
	}

	/**
	 * @param proof
	 * @return {@link Proof} that caches all {@link Proof#getInferences(Object)}
	 *         requests of the input {@link Proof}
	 */
	public static <I extends Inference<?>> Proof<I> cache(
			Proof<? extends I> proof) {
		return new CachingProof<I>(proof);
	}

	/**
	 * @param proof
	 * @return {@link DynamicProof} that caches all
	 *         {@link DynamicProof#getInferences(Object)} requests of the input
	 *         {@link DynamicProof}, until the input proof changes
	 */
	public static <I extends Inference<?>> DynamicProof<I> cache(
			DynamicProof<? extends I> proof) {
		return new CachingDynamicProof<I>(proof);
	}

	/**
	 * Recursively enumerates all inferences of the given {@link Proof} starting
	 * from the inferences for the given goal conclusion and then proceeding to
	 * the inferences of their premises. The encountered inferences are
	 * processed using the provided {@link Consumer}. The inferences for each
	 * conclusion are enumerated only once even if the conclusion appears as
	 * premise in several inferences.
	 * 
	 * @param proof
	 * @param goal
	 * @param follow
	 * @return the set of all conclusions for which the inferences were
	 *         enumerated
	 */
	public static <T, I extends Inference<? extends T>> Set<T> unfoldRecursively(
			Proof<I> proof, T goal, Predicate<? super I> follow) {
		return Proofs.<T, I> unfoldRecursively(proof, goal, follow,
				new HashSet<>());
	}

	public static <C, I extends Inference<? extends C>> Set<C> unfoldRecursively(
			Proof<I> proof, C goal, Predicate<? super I> follow,
			Set<C> result) {
		if (!result.add(goal)) {
			return result;
		}
		Queue<C> toExpand = new ArrayDeque<>();
		toExpand.add(goal);
		for (;;) {
			C next = toExpand.poll();
			if (next == null) {
				return result;
			}
			for (I inf : proof.getInferences(next)) {
				if (follow.test(inf)) {
					for (C premise : inf.getPremises()) {
						if (result.add(premise)) {
							toExpand.add(premise);
						}
					}
				}
			}
		}
	}

	/**
	 * @param proof
	 * @param goal
	 * @return the number of inferences in the proof that is used for deriving
	 *         the given goal
	 */
	public static int countInferences(Proof<?> proof, Object goal) {
		final int[] counter = { 0 };
		unfoldRecursively(proof, goal, inf -> {
			counter[0]++;
			return true;
		});
		return counter[0];
	}

	/**
	 * @param proof
	 * @param goal
	 * @return the set of conclusions without which the goal would not be
	 *         derivable using the proof inferences; i.e., every derivation
	 *         using the inferences must use every essential axiom
	 */
	public static <A, I extends AxiomPinpointingInference<?, ? extends A>> Set<A> getEssentialAxioms(
			Proof<I> proof, Object goal) {
		Set<A> result = new HashSet<>();
		IncrementalDerivabilityChecker<A, I> checker = new DerivabilityCheckerUP<>(
				proof);
		List<A> axioms = new ArrayList<>();
		unfoldRecursively(proof, goal, inf -> {
			inf.getJustification().forEach(ax -> {
				if (checker.addAxiom(ax)) {
					axioms.add(ax);
				}
			});
			return true;
		});
		for (A axiom : axioms) {
			checker.removeAxiom(axiom);
			if (!checker.isDerivable(goal)) {
				result.add(axiom);
			}
			checker.addAxiom(axiom);
		}
		return result;
	}

	/**
	 * Adds to the set of conclusions all conclusions that are derived from them
	 * using the inferences of the given proof that can be used for proving the
	 * given goal; produces the applied inferences using the given consumer
	 * 
	 * @param derivable
	 * @param proof
	 * @param goal
	 * @param applied
	 */
	public static <C, I extends Inference<? extends C>> void expand(
			Set<C> derivable, Proof<? extends I> proof, C goal,
			Consumer<? super I> applied) {
		InferenceExpander.<C, I> expand(derivable, proof, goal, applied);
	}

	/**
	 * Verifies that the inferences of the given proof for deriving the given
	 * are not cyclic. A set of inferences is cyclic if every inference in this
	 * set has at least one premise that is a conclusion of some inference in
	 * this set.
	 *
	 * @param <C>
	 * @param <I>
	 * @param proof
	 * @param goal
	 * @param derived
	 *            a consumer which receives the notification about the derived
	 *            conclusions of this proof: each notified conclusion is derived
	 *            by some proof inference whose premises were notified by this
	 *            consumer before; each derived conclusion receives at most one
	 *            notification; if the proof is acyclic and derives the goal,
	 *            the last conclusion notified by the consumer will be goal
	 *
	 * @return {@code null} if the set of the proof inferences is not cyclic, or
	 *         the set of conclusions containing the goal such that each element
	 *         in this set is a conclusion of some proof inference that contains
	 *         a premise from this set (the set of these inferences is cyclic).
	 */
	public static <C, I extends Inference<? extends C>> Set<C> checkAcyclicity(
			Proof<I> proof, C goal, Consumer<? super C> derived) {
		Deque<C> dfs = new ArrayDeque<>();
		dfs.add(goal);
		Set<C> expanded = Sets.newHashSet();
		Set<C> path = Sets.newHashSet();
		for (;;) {
			C next = dfs.peekLast();
			if (next == null) {
				return null;
			}
			if (expanded.add(next)) {
				path.add(next);
				for (I inf : proof.getInferences(next)) {
					for (C c : inf.getPremises()) {
						if (path.contains(c)) {
							return path; // cycle on the path!
						}
						dfs.addLast(c);
					}
				}
			} else {
				dfs.removeLast();
				if (path.remove(next)) {
					derived.accept(next);
				}
			}
		}
	}

	/**
	 * @param proof
	 * @param goal
	 * @return a proof obtained from the given proofs by removing some
	 *         inferences that do not have effect on the derivation relation
	 *         between the asserted conclusions in the proof (derived by
	 *         asserted inferences) and the goal conclusion; i.e., if the goal
	 *         conclusion was derivable from some subset of asserted conclusions
	 *         using original inferences, then it is also derivable using the
	 *         returned proof
	 * @see Inferences#isAsserted(Inference)
	 */
	public static <I extends AxiomPinpointingInference<?, ?>> Proof<I> prune(
			Proof<? extends I> proof, Object goal) {
		return new PrunedProof<I>(proof, goal);
	}

	/**
	 * @param <Q>
	 * @param <I>
	 * @param prover
	 * @return a prover returning pruned proofs of the given prover
	 */
	public static <Q, I extends AxiomPinpointingInference<?, ?>> Prover<Q, I> prune(
			Prover<? super Q, ? extends I> prover) {
		return query -> prune(prover.getProof(query), query);
	}

	/**
	 * Recursively prints all inferences for the derived goal and the premises
	 * of such inferences to the standard output using ASCII characters. Due to
	 * potential cycles, inferences for every conclusion are printed only once
	 * upon their first occurrence in the proof. Every following occurrence of
	 * the same conclusion is labeled by {@code *}.
	 * 
	 * @param proof
	 *            the {@link Proof} from which to take the inferences
	 * @param goal
	 *            the conclusion starting from which the inferences are printed
	 */
	public static void print(Proof<?> proof, Object goal) {
		try {
			ProofPrinter.print(proof, goal);
		} catch (IOException e) {
			throw new RuntimeException("Exception while printing the proof", e);
		}

	}

}
