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

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.function.Predicate;

import org.junit.Test;

/**
 * @author Pavel Klinov
 *
 *         pavel.klinov@uni-ulm.de
 * 
 * @author Yevgeny Kazakov
 */
public class ProofTest {

	@Test
	public void proofTest() {
		ProofBuilder<Integer, ?, ?> b = new BaseProofBuilder<>();
		b.conclusion(1).premise(2).add();
		b.conclusion(2).premise(3).premise(4).add();
		b.conclusion(2).premise(5).premise(6).add();
		Proof<? extends Inference<Integer>> p = b.getProof();
		assertEquals(1, p.getInferences(1).size());
		assertEquals(2, p.getInferences(2).size());
		assertEquals(0, p.getInferences(3).size());
	}

	@Test
	public void derivabilityTestCycle() throws Exception {
		ProofBuilder<String, ?, ?> b = new BaseProofBuilder<>();
		b.conclusion("A").premise("B").add();
		b.conclusion("A").premise("C").premise("D").add();
		b.conclusion("C").premise("B").add();
		b.conclusion("C").add();
		b.conclusion("B").premise("C").add();
		assertTrue(Proofs.isDerivable(b.getProof(), "A"));
	}

	@Test
	public void blockCyclicProof() throws Exception {
		ProofBuilder<String, ?, ?> b = new BaseProofBuilder<>();
		b.conclusion("A ⊑ B").premise("A ⊑ B ⊓ C").add();
		b.conclusion("A ⊑ B").premise("A ⊑ C").premise("C ⊑ B").add();
		b.conclusion("A ⊑ C").premise("A ⊑ D").premise("D ⊑ C").add();
		b.conclusion("A ⊑ D").premise("A ⊑ B").premise("B ⊑ D").add();
		b.conclusion("A ⊑ B ⊓ C").add();
		b.conclusion("B ⊑ D").add();
		b.conclusion("D ⊑ C").add();
		b.conclusion("C ⊑ B").add();

		Proof<? extends Inference<String>> p = b.getProof();

		assertTrue(ProofNodes.isDerivable(ProofNodes.create(p, "A ⊑ C")));

		ProofNode<String> root = ProofNodes.create(p, "A ⊑ B");

		assertTrue(ProofNodes.isDerivable(root));

		assertEquals(2,
				ProofNodes.eliminateNotDerivable(root).getInferences().size());

		// only one inference remains since the other is cyclic
		assertEquals(1, ProofNodes.eliminateNotDerivableAndCycles(root)
				.getInferences().size());

		// testing the same but using derivability "from" methods

		root = ProofNodes.create(p, "A ⊑ B");
		assertTrue(ProofNodes.isDerivable(root));

		assertEquals(2,
				ProofNodes.eliminateNotDerivable(root).getInferences().size());

		// only one inference remains since the other is cyclic
		assertEquals(1, ProofNodes.eliminateNotDerivableAndCycles(root)
				.getInferences().size());

	}

	@Test
	public void testDerivabilityCheckerWithBlocking0() throws Exception {
		ProofBuilder<Integer, ?, ?> b = new BaseProofBuilder<>();
		b.conclusion(0).premise(1).add();
		b.conclusion(1).premise(2).add();
		b.conclusion(11).premise(2).add();
		b.conclusion(2).add();

		Proof<AxiomPinpointingInference<Integer, Integer>> p = Proofs
				.transform(b.getProof(), Proofs::justifyByConclusion);
		IncrementalDerivabilityChecker<Integer, ?> checker = new DerivabilityCheckerUP<>(
				p);

		Set<Integer> axioms = new HashSet<>();

		addAxiom(axioms, checker, 0);
		addAxiom(axioms, checker, 1);
		addAxiom(axioms, checker, 11);
		addAxiom(axioms, checker, 2);

		assertDerivable(checker, 0);
		removeAxiom(axioms, checker, 2);
		assertNotDerivable(checker, 0);
		removeAxiom(axioms, checker, 1);
		addAxiom(axioms, checker, 2);
		assertDerivable(checker, 11);
		assertNotDerivable(checker, 0);
		addAxiom(axioms, checker, 1);
		assertDerivable(checker, 0);
	}

	@Test
	public void testDerivabilityCheckerWithBlocking1() throws Exception {
		ProofBuilder<Integer, ?, ?> b = new BaseProofBuilder<>();
		b.conclusion(0).premise(11).premise(22).add();
		b.conclusion(11).premise(1).add();
		b.conclusion(22).premise(2).add();
		b.conclusion(1).add();
		b.conclusion(2).add();

		Proof<AxiomPinpointingInference<Integer, Integer>> p = Proofs
				.transform(b.getProof(), Proofs::justifyByConclusion);
		IncrementalDerivabilityChecker<Integer, ?> checker = new DerivabilityCheckerUP<>(
				p);

		Set<Integer> axioms = new HashSet<>();

		addAxiom(axioms, checker, 0);
		addAxiom(axioms, checker, 11);
		addAxiom(axioms, checker, 22);
		addAxiom(axioms, checker, 1);
		addAxiom(axioms, checker, 2);

		assertDerivable(checker, 0);
		removeAxiom(axioms, checker, 2);
		assertNotDerivable(checker, 0);
		removeAxiom(axioms, checker, 1);
		addAxiom(axioms, checker, 2);
		assertNotDerivable(checker, 0);
		addAxiom(axioms, checker, 1);
		assertDerivable(checker, 0);
	}

	@Test
	public void testDerivabilityCheckerWithBlocking2() throws Exception {
		ProofBuilder<Integer, ?, ?> b = new BaseProofBuilder<>();
		b.conclusion(0).premise(1).premise(2).add();
		b.conclusion(0).premise(3).premise(4).add();
		b.conclusion(2).premise(0).premise(0).add();
		b.conclusion(1).premise(3).premise(4).add();
		b.conclusion(3).add();
		b.conclusion(4).add();

		Proof<AxiomPinpointingInference<Integer, Integer>> p = Proofs
				.transform(b.getProof(), Proofs::justifyByConclusion);
		IncrementalDerivabilityChecker<Integer, ?> checker = new DerivabilityCheckerUP<>(
				p);

		Set<Integer> axioms = new HashSet<>();

		addAxiom(axioms, checker, 0);
		addAxiom(axioms, checker, 1);
		addAxiom(axioms, checker, 2);		
		addAxiom(axioms, checker, 3);
		addAxiom(axioms, checker, 4);

		assertDerivable(checker, 0);
		removeAxiom(axioms, checker, 1);
		assertDerivable(checker, 0);
		addAxiom(axioms, checker, 1);
		removeAxiom(axioms, checker, 3);
		assertNotDerivable(checker, 0);
		assertNotDerivable(checker, 3);
		assertDerivable(checker, 4);
		addAxiom(axioms, checker, 3);
		assertDerivable(checker, 0);
		assertDerivable(checker, 3);
		assertDerivable(checker, 4);
		removeAxiom(axioms, checker, 4);
		assertNotDerivable(checker, 0);
		assertDerivable(checker, 3);
		assertNotDerivable(checker, 4);
	}

	@Test
	public void testDerivabilityCheckerWithBlocking3() throws Exception {
		ProofBuilder<Integer, ?, ?> b = new BaseProofBuilder<>();
		b.conclusion(0).premise(1).add();
		b.conclusion(0).premise(2).add();
		b.conclusion(1).add();
		b.conclusion(2).add();

		Proof<AxiomPinpointingInference<Integer, Integer>> p = Proofs
				.transform(b.getProof(), Proofs::justifyByConclusion);
		IncrementalDerivabilityChecker<Integer, ?> checker = new DerivabilityCheckerUP<>(
				p);

		Set<Integer> axioms = new HashSet<>();

		addAxiom(axioms, checker, 0);
		addAxiom(axioms, checker, 1);
		addAxiom(axioms, checker, 2);

		removeAxiom(axioms, checker, 1);
		assertDerivable(checker, 0);
		addAxiom(axioms, checker, 1);
		removeAxiom(axioms, checker, 2);
		assertDerivable(checker, 0);
		removeAxiom(axioms, checker, 1);
		assertNotDerivable(checker, 0);
		addAxiom(axioms, checker, 1);
		addAxiom(axioms, checker, 2);
		assertDerivable(checker, 0);
	}

	@Test
	public void testDerivabilityCheckerWithBlocking4() throws Exception {
		ProofBuilder<Integer, ?, ?> b = new BaseProofBuilder<>();

		b.conclusion(0).premise(1).add();
		b.conclusion(1).premise(0).add();
		b.conclusion(0).add();

		Proof<AxiomPinpointingInference<Integer, Integer>> p = Proofs
				.transform(b.getProof(), Proofs::justifyByConclusion);
		IncrementalDerivabilityChecker<Integer, ?> checker = new DerivabilityCheckerUP<>(
				p);

		checker.addAxiom(0);
		checker.addAxiom(1);

		assertDerivable(checker, 0);
	}

	@Test
	public void blockCyclicProof2() throws Exception {
		BaseProofBuilder<Integer, ?> b = new BaseProofBuilder<>();
		b.conclusion(0).premise(1).premise(2).add();
		b.conclusion(0).premise(3).premise(4).add();
		b.conclusion(2).premise(0).premise(0).add();
		b.conclusion(1).add();
		b.conclusion(3).add();
		b.conclusion(4).add();
		Proof<? extends Inference<Integer>> p = b.getProof();

		ProofNode<Integer> root = ProofNodes.create(p, 0);

		assertTrue(ProofNodes.isDerivable(root));

		// everything is derivable
		assertEquals(2,
				ProofNodes.eliminateNotDerivable(root).getInferences().size());

		assertTrue(ProofNodes.isDerivable(root));

		assertTrue(ProofNodes
				.isDerivable(ProofNodes.eliminateNotDerivableAndCycles(root)));

		// only one inference remains since the other is cyclic
		assertEquals(1, ProofNodes.eliminateNotDerivableAndCycles(root)
				.getInferences().size());

		// the same using derivability "from"

		root = ProofNodes.create(p, 0);

		assertTrue(ProofNodes.isDerivable(root));

		assertEquals(2,
				ProofNodes.eliminateNotDerivable(root).getInferences().size());

		// only one inference remains since the other is cyclic
		assertEquals(1, ProofNodes.eliminateNotDerivableAndCycles(root)
				.getInferences().size());

	}

	@Test
	public void recursiveBlocking() throws Exception {
		BaseProofBuilder<Integer, ?> b = new BaseProofBuilder<>();
		b.conclusion(0).premise(1).premise(2).add();
		b.conclusion(1).premise(3).premise(4).premise(5).add();
		b.conclusion(3).premise(6).premise(7).add();
		b.conclusion(4).premise(8).premise(9).add();
		b.conclusion(2).add();
		b.conclusion(5).add();
		b.conclusion(7).add();
		b.conclusion(8).add();
		b.conclusion(9).add();
		Proof<? extends Inference<Integer>> p1 = b.getProof();

		b = new BaseProofBuilder<>();
		b.conclusion(6).add();
		Proof<? extends Inference<Integer>> p2 = b.getProof();

		ProofNode<Integer> root = ProofNodes.create(p1, 0);

		// not derivable
		assertEquals(null, ProofNodes.eliminateNotDerivable(root));

		root = ProofNodes.create(Proofs.union(p1, p2), 0);

		// derivable

		assertEquals(1,
				ProofNodes.eliminateNotDerivable(root).getInferences().size());

	}

	public static <I extends Inference<?>> void assertDerivation(Proof<I> proof,
			Object goal) {
		Object[] last = { null };
		Set<Object> cycle = Proofs.checkAcyclicity(proof, goal, c -> {
			last[0] = c;
		});
		if (cycle != null) {
			int size = cycle.size();
			List<I> inferenceCycle = new ArrayList<>(size);
			Object next = goal;
			main_loop: for (int i = 0; i < size; i++) {
				for (I inf : proof.getInferences(next)) {
					for (Object c : inf.getPremises()) {
						if (cycle.contains(c)) {
							inferenceCycle.add(inf);
							next = c;
							continue main_loop;
						}
					}
				}
			}
			fail("Cyclic proof: " + inferenceCycle);
		}
		assertEquals("Not derived: " + goal, last[0], goal);
	}

	static void assertDerivable(DerivabilityChecker<?> checker, Object goal) {
		assertTrue(checker.isDerivable(goal));
		assertDerivation(checker.explainIsDerivable(goal), goal);
	}

	public static <A> void assertNotDerivable(DerivabilityChecker<?> checker,
			Object goal) {
		assertFalse(checker.isDerivable(goal));
		Proof<?> explanation = checker.explainIsDerivable(goal);
		// remove inferences whose conclusion are derivable
		Proof<?> filtered = Proofs.filter(checker.getProof(),
				inf -> !explanation.getInferences(inf.getConclusion())
						.isEmpty());
		// check that at least one premise of the remaining inferences is not
		// derivable
		Proofs.unfoldRecursively(filtered, goal, inf -> {
			if (!inf.getPremises().stream()
					.anyMatch(c -> explanation.getInferences(c).isEmpty())) {
				fail("All premises of inferences are derivable but the conclusion is not: "
						+ inf);
			}
			return false;
		});
	}

	private static <A> void addAxiom(Set<A> axioms,
			IncrementalDerivabilityChecker<A, ? extends AxiomPinpointingInference<?, ? extends A>> checker,
			A axiom) {
		axioms.add(axiom);
		checker.addAxiom(axiom);
		assertJustified(checker.getProof(), axiom, axioms::contains);
	}

	private static <A> void removeAxiom(Set<A> axioms,
			IncrementalDerivabilityChecker<A, ? extends AxiomPinpointingInference<?, ? extends A>> checker,
			A axiom) {
		axioms.remove(axiom);
		checker.removeAxiom(axiom);
		assertJustified(checker.getProof(), axiom, axioms::contains);
	}

	public static <A> void assertJustified(
			Proof<? extends AxiomPinpointingInference<?, ? extends A>> proof,
			Object goal, Predicate<A> isAxiom) {
		Proofs.unfoldRecursively(proof, goal, inf -> {
			inf.getJustification()
					.forEach(ax -> assertTrue("Inference " + inf
							+ " uses invalid justification " + ax,
							isAxiom.test(ax)));
			return true;
		});
	}

	public static <A> void assertDerivable(
			IncrementalDerivabilityChecker<?, ? extends AxiomPinpointingInference<?, ? extends A>> checker,
			Object goal, Predicate<A> isAxiom) {
		assertDerivable(checker, goal);
		Proof<? extends AxiomPinpointingInference<?, ? extends A>> proof = checker.explainIsDerivable(goal);
		assertJustified(proof, goal, isAxiom);
	}

}
