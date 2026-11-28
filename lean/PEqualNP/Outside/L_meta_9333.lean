import PEqualNP.Outside.L_meta_8463
import PEqualNP.Outside.L_meta_8465
import PEqualNP.Outside.L_meta_8467
import PEqualNP.Outside.L_meta_8614
import PEqualNP.Outside.L_meta_8615
import PEqualNP.Outside.L_meta_8616
import PEqualNP.Outside.L_meta_8617
import PEqualNP.Outside.L_meta_8618
import PEqualNP.Outside.L_meta_8619
import PEqualNP.Outside.L_meta_8620
import PEqualNP.Outside.L_meta_8621
import PEqualNP.Outside.L_meta_8622
import PEqualNP.Outside.L_meta_8623
import PEqualNP.Outside.L_meta_8624
import PEqualNP.Outside.L_meta_8625
import PEqualNP.Outside.L_meta_8626
import PEqualNP.Outside.L_meta_8627
import PEqualNP.Outside.L_meta_8628
import PEqualNP.Outside.L_meta_8629
import PEqualNP.Outside.L_meta_8630
import PEqualNP.Outside.L_meta_8631
import PEqualNP.Outside.L_meta_8632
import PEqualNP.Outside.L_meta_8633
import PEqualNP.Outside.L_meta_8634
import PEqualNP.Outside.L_meta_8635
import PEqualNP.Outside.L_meta_8636
import PEqualNP.Outside.L_meta_8637
import PEqualNP.Outside.L_meta_8638
import PEqualNP.Outside.L_meta_8639
import PEqualNP.Outside.L_meta_8640
import PEqualNP.Outside.L_meta_8641
import PEqualNP.Outside.L_meta_8642
import PEqualNP.Outside.L_meta_8643
import PEqualNP.Outside.L_meta_8644
import PEqualNP.Outside.L_meta_8645
import PEqualNP.Outside.L_meta_8646
import PEqualNP.Outside.L_meta_8647
import PEqualNP.Outside.L_meta_8648
import PEqualNP.Outside.L_meta_8649
import PEqualNP.Outside.L_meta_8650
import PEqualNP.Outside.L_meta_8651
import PEqualNP.Outside.L_meta_8652
import PEqualNP.Outside.L_meta_8653
import PEqualNP.Outside.L_meta_8654
import PEqualNP.Outside.L_meta_8655
import PEqualNP.Outside.L_meta_8656
import PEqualNP.Outside.L_meta_8657
import PEqualNP.Outside.L_meta_8658
import PEqualNP.Outside.L_meta_8659
import PEqualNP.Outside.L_meta_8660
import PEqualNP.Outside.L_meta_8661
import PEqualNP.Outside.L_meta_8662
import PEqualNP.Outside.L_meta_8663
import PEqualNP.Outside.L_meta_8664
import PEqualNP.Outside.L_meta_8665
import PEqualNP.Outside.L_meta_8666
import PEqualNP.Outside.L_meta_8667
import PEqualNP.Outside.L_meta_8668
import PEqualNP.Outside.L_meta_8669
import PEqualNP.Outside.L_meta_8670
import PEqualNP.Outside.L_meta_8671
import PEqualNP.Outside.L_meta_8672
import PEqualNP.Outside.L_meta_8673
import PEqualNP.Outside.L_meta_8674
import PEqualNP.Outside.L_meta_8675
import PEqualNP.Outside.L_meta_8676
import PEqualNP.Outside.L_meta_8677
import PEqualNP.Outside.L_meta_8678
import PEqualNP.Outside.L_meta_8679
import PEqualNP.Outside.L_meta_8680
import PEqualNP.Outside.L_meta_8681
import PEqualNP.Outside.L_meta_8682
import PEqualNP.Outside.L_meta_8683
import PEqualNP.Outside.L_meta_8684
import PEqualNP.Outside.L_meta_8685
import PEqualNP.Outside.L_meta_8686
import PEqualNP.Outside.L_meta_8687
import PEqualNP.Outside.L_meta_8688
import PEqualNP.Outside.L_meta_8689
import PEqualNP.Outside.L_meta_8690
import PEqualNP.Outside.L_meta_8691
import PEqualNP.Outside.L_meta_8692
import PEqualNP.Outside.L_meta_8693
import PEqualNP.Outside.L_meta_8694
import PEqualNP.Outside.L_meta_8695
import PEqualNP.Outside.L_meta_8696
import PEqualNP.Outside.L_meta_8697
import PEqualNP.Outside.L_meta_8698
import PEqualNP.Outside.L_meta_8699
import PEqualNP.Outside.L_meta_8700
import PEqualNP.Outside.L_meta_8701
import PEqualNP.Outside.L_meta_8702
import PEqualNP.Outside.L_meta_8703
import PEqualNP.Outside.L_meta_8704
import PEqualNP.Outside.L_meta_8705
import PEqualNP.Outside.L_meta_8706
import PEqualNP.Outside.L_meta_8707
import PEqualNP.Outside.L_meta_8708
import PEqualNP.Outside.L_meta_8709
import PEqualNP.Outside.L_meta_8710
import PEqualNP.Outside.L_meta_8711
import PEqualNP.Outside.L_meta_8712
import PEqualNP.Outside.L_meta_8713
import PEqualNP.Outside.L_meta_8714
import PEqualNP.Outside.L_meta_8715
import PEqualNP.Outside.L_meta_8716
import PEqualNP.Outside.L_meta_8717
import PEqualNP.Outside.L_meta_8718
import PEqualNP.Outside.L_meta_8719
import PEqualNP.Outside.L_meta_8720
import PEqualNP.Outside.L_meta_8721
import PEqualNP.Outside.L_meta_8722
import PEqualNP.Outside.L_meta_8723
import PEqualNP.Outside.L_meta_8724
import PEqualNP.Outside.L_meta_8729
import PEqualNP.Library.Mono5Assembly

set_option maxRecDepth 20000 in
/-- Every monotone function of five inputs: NOT gates save nothing. Closing file: L-meta-8613 applied to the outside proofs of the
listed rows, one for each of the 210 classes. -/
theorem PEqualNP.Outside.L_meta_9333 : ∀ f : (Fin 5 → Bool) → Bool, (∀ x y : Fin 5 → Bool, (∀ i, x i = true → y i = true) → f x = true → f y = true) → ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 5 f s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = f x := by
  apply PEqualNP.Library.Mono5Assembly
  intro T hT
  simp only [Finset.mem_insert, Finset.mem_singleton] at hT
  rcases hT with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact PEqualNP.Outside.L_meta_8621
  · exact PEqualNP.Outside.L_meta_8622
  · exact PEqualNP.Outside.L_meta_8624
  · exact PEqualNP.Outside.L_meta_8626
  · exact PEqualNP.Outside.L_meta_8628
  · exact PEqualNP.Outside.L_meta_8630
  · exact PEqualNP.Outside.L_meta_8631
  · exact PEqualNP.Outside.L_meta_8632
  · exact PEqualNP.Outside.L_meta_8633
  · exact PEqualNP.Outside.L_meta_8634
  · exact PEqualNP.Outside.L_meta_8635
  · exact PEqualNP.Outside.L_meta_8636
  · exact PEqualNP.Outside.L_meta_8637
  · exact PEqualNP.Outside.L_meta_8638
  · exact PEqualNP.Outside.L_meta_8639
  · exact PEqualNP.Outside.L_meta_8640
  · exact PEqualNP.Outside.L_meta_8641
  · exact PEqualNP.Outside.L_meta_8642
  · exact PEqualNP.Outside.L_meta_8643
  · exact PEqualNP.Outside.L_meta_8644
  · exact PEqualNP.Outside.L_meta_8645
  · exact PEqualNP.Outside.L_meta_8646
  · exact PEqualNP.Outside.L_meta_8647
  · exact PEqualNP.Outside.L_meta_8648
  · exact PEqualNP.Outside.L_meta_8649
  · exact PEqualNP.Outside.L_meta_8650
  · exact PEqualNP.Outside.L_meta_8651
  · exact PEqualNP.Outside.L_meta_8652
  · exact PEqualNP.Outside.L_meta_8653
  · exact PEqualNP.Outside.L_meta_8654
  · exact PEqualNP.Outside.L_meta_8655
  · exact PEqualNP.Outside.L_meta_8656
  · exact PEqualNP.Outside.L_meta_8657
  · exact PEqualNP.Outside.L_meta_8658
  · exact PEqualNP.Outside.L_meta_8659
  · exact PEqualNP.Outside.L_meta_8661
  · exact PEqualNP.Outside.L_meta_8662
  · exact PEqualNP.Outside.L_meta_8664
  · exact PEqualNP.Outside.L_meta_8668
  · exact PEqualNP.Outside.L_meta_8670
  · exact PEqualNP.Outside.L_meta_8672
  · exact PEqualNP.Outside.L_meta_8674
  · exact PEqualNP.Outside.L_meta_8676
  · exact PEqualNP.Outside.L_meta_8678
  · exact PEqualNP.Outside.L_meta_8680
  · exact PEqualNP.Outside.L_meta_8682
  · exact PEqualNP.Outside.L_meta_8684
  · exact PEqualNP.Outside.L_meta_8686
  · exact PEqualNP.Outside.L_meta_8688
  · exact PEqualNP.Outside.L_meta_8690
  · exact PEqualNP.Outside.L_meta_8692
  · exact PEqualNP.Outside.L_meta_8693
  · exact PEqualNP.Outside.L_meta_8695
  · exact PEqualNP.Outside.L_meta_8696
  · exact PEqualNP.Outside.L_meta_8698
  · exact PEqualNP.Outside.L_meta_8660
  · exact PEqualNP.Outside.L_meta_8663
  · exact PEqualNP.Outside.L_meta_8665
  · exact PEqualNP.Outside.L_meta_8666
  · exact PEqualNP.Outside.L_meta_8667
  · exact PEqualNP.Outside.L_meta_8669
  · exact PEqualNP.Outside.L_meta_8671
  · exact PEqualNP.Outside.L_meta_8673
  · exact PEqualNP.Outside.L_meta_8675
  · exact PEqualNP.Outside.L_meta_8677
  · exact PEqualNP.Outside.L_meta_8679
  · exact PEqualNP.Outside.L_meta_8681
  · exact PEqualNP.Outside.L_meta_8683
  · exact PEqualNP.Outside.L_meta_8685
  · exact PEqualNP.Outside.L_meta_8687
  · exact PEqualNP.Outside.L_meta_8689
  · exact PEqualNP.Outside.L_meta_8691
  · exact PEqualNP.Outside.L_meta_8694
  · exact PEqualNP.Outside.L_meta_8697
  · exact PEqualNP.Outside.L_meta_8699
  · exact PEqualNP.Outside.L_meta_8700
  · exact PEqualNP.Outside.L_meta_8701
  · exact PEqualNP.Outside.L_meta_8702
  · exact PEqualNP.Outside.L_meta_8703
  · exact PEqualNP.Outside.L_meta_8704
  · exact PEqualNP.Outside.L_meta_8705
  · exact PEqualNP.Outside.L_meta_8706
  · exact PEqualNP.Outside.L_meta_8707
  · exact PEqualNP.Outside.L_meta_8708
  · exact PEqualNP.Outside.L_meta_8709
  · exact PEqualNP.Outside.L_meta_8710
  · exact PEqualNP.Outside.L_meta_8711
  · exact PEqualNP.Outside.L_meta_8712
  · exact PEqualNP.Outside.L_meta_8713
  · exact PEqualNP.Outside.L_meta_8714
  · exact PEqualNP.Outside.L_meta_8715
  · exact PEqualNP.Outside.L_meta_8716
  · exact PEqualNP.Outside.L_meta_8717
  · exact PEqualNP.Outside.L_meta_8718
  · exact PEqualNP.Outside.L_meta_8719
  · exact PEqualNP.Outside.L_meta_8720
  · exact PEqualNP.Outside.L_meta_8721
  · exact PEqualNP.Outside.L_meta_8722
  · exact PEqualNP.Outside.L_meta_8723
  · exact PEqualNP.Outside.L_meta_8724
  · exact PEqualNP.Outside.L_meta_8729
  · exact PEqualNP.Outside.L_meta_8614 _ (by decide)
  · exact PEqualNP.Outside.L_meta_8614 _ (by decide)
  · exact PEqualNP.Outside.L_meta_8614 _ (by decide)
  · exact PEqualNP.Outside.L_meta_8614 _ (by decide)
  · exact PEqualNP.Outside.L_meta_8614 _ (by decide)
  · exact PEqualNP.Outside.L_meta_8614 _ (by decide)
  · exact PEqualNP.Outside.L_meta_8614 _ (by decide)
  · exact PEqualNP.Outside.L_meta_8614 _ (by decide)
  · exact PEqualNP.Outside.L_meta_8614 _ (by decide)
  · exact PEqualNP.Outside.L_meta_8614 _ (by decide)
  · exact PEqualNP.Outside.L_meta_8615 _ (by decide)
  · exact PEqualNP.Outside.L_meta_8615 _ (by decide)
  · exact PEqualNP.Outside.L_meta_8615 _ (by decide)
  · exact PEqualNP.Outside.L_meta_8615 _ (by decide)
  · exact PEqualNP.Outside.L_meta_8615 _ (by decide)
  · exact PEqualNP.Outside.L_meta_8615 _ (by decide)
  · exact PEqualNP.Outside.L_meta_8615 _ (by decide)
  · exact PEqualNP.Outside.L_meta_8615 _ (by decide)
  · exact PEqualNP.Outside.L_meta_8615 _ (by decide)
  · exact PEqualNP.Outside.L_meta_8615 _ (by decide)
  · exact PEqualNP.Outside.L_meta_8616 _ (by decide)
  · exact PEqualNP.Outside.L_meta_8616 _ (by decide)
  · exact PEqualNP.Outside.L_meta_8616 _ (by decide)
  · exact PEqualNP.Outside.L_meta_8616 _ (by decide)
  · exact PEqualNP.Outside.L_meta_8616 _ (by decide)
  · exact PEqualNP.Outside.L_meta_8616 _ (by decide)
  · exact PEqualNP.Outside.L_meta_8616 _ (by decide)
  · exact PEqualNP.Outside.L_meta_8616 _ (by decide)
  · exact PEqualNP.Outside.L_meta_8616 _ (by decide)
  · exact PEqualNP.Outside.L_meta_8616 _ (by decide)
  · exact PEqualNP.Outside.L_meta_8617 _ (by decide)
  · exact PEqualNP.Outside.L_meta_8617 _ (by decide)
  · exact PEqualNP.Outside.L_meta_8617 _ (by decide)
  · exact PEqualNP.Outside.L_meta_8617 _ (by decide)
  · exact PEqualNP.Outside.L_meta_8617 _ (by decide)
  · exact PEqualNP.Outside.L_meta_8617 _ (by decide)
  · exact PEqualNP.Outside.L_meta_8617 _ (by decide)
  · exact PEqualNP.Outside.L_meta_8617 _ (by decide)
  · exact PEqualNP.Outside.L_meta_8617 _ (by decide)
  · exact PEqualNP.Outside.L_meta_8617 _ (by decide)
  · exact PEqualNP.Outside.L_meta_8618 _ (by decide)
  · exact PEqualNP.Outside.L_meta_8618 _ (by decide)
  · exact PEqualNP.Outside.L_meta_8618 _ (by decide)
  · exact PEqualNP.Outside.L_meta_8618 _ (by decide)
  · exact PEqualNP.Outside.L_meta_8618 _ (by decide)
  · exact PEqualNP.Outside.L_meta_8618 _ (by decide)
  · exact PEqualNP.Outside.L_meta_8618 _ (by decide)
  · exact PEqualNP.Outside.L_meta_8618 _ (by decide)
  · exact PEqualNP.Outside.L_meta_8618 _ (by decide)
  · exact PEqualNP.Outside.L_meta_8618 _ (by decide)
  · exact PEqualNP.Outside.L_meta_8619 _ (by decide)
  · exact PEqualNP.Outside.L_meta_8619 _ (by decide)
  · exact PEqualNP.Outside.L_meta_8619 _ (by decide)
  · exact PEqualNP.Outside.L_meta_8619 _ (by decide)
  · exact PEqualNP.Outside.L_meta_8619 _ (by decide)
  · exact PEqualNP.Outside.L_meta_8619 _ (by decide)
  · exact PEqualNP.Outside.L_meta_8619 _ (by decide)
  · exact PEqualNP.Outside.L_meta_8619 _ (by decide)
  · exact PEqualNP.Outside.L_meta_8619 _ (by decide)
  · exact PEqualNP.Outside.L_meta_8619 _ (by decide)
  · exact PEqualNP.Outside.L_meta_8620 _ (by decide)
  · exact PEqualNP.Outside.L_meta_8620 _ (by decide)
  · exact PEqualNP.Outside.L_meta_8620 _ (by decide)
  · exact PEqualNP.Outside.L_meta_8620 _ (by decide)
  · exact PEqualNP.Outside.L_meta_8620 _ (by decide)
  · exact PEqualNP.Outside.L_meta_8620 _ (by decide)
  · exact PEqualNP.Outside.L_meta_8620 _ (by decide)
  · exact PEqualNP.Outside.L_meta_8620 _ (by decide)
  · exact PEqualNP.Outside.L_meta_8620 _ (by decide)
  · exact PEqualNP.Outside.L_meta_8620 _ (by decide)
  · exact PEqualNP.Outside.L_meta_8623 _ (by decide)
  · exact PEqualNP.Outside.L_meta_8623 _ (by decide)
  · exact PEqualNP.Outside.L_meta_8623 _ (by decide)
  · exact PEqualNP.Outside.L_meta_8623 _ (by decide)
  · exact PEqualNP.Outside.L_meta_8623 _ (by decide)
  · exact PEqualNP.Outside.L_meta_8623 _ (by decide)
  · exact PEqualNP.Outside.L_meta_8623 _ (by decide)
  · exact PEqualNP.Outside.L_meta_8623 _ (by decide)
  · exact PEqualNP.Outside.L_meta_8623 _ (by decide)
  · exact PEqualNP.Outside.L_meta_8623 _ (by decide)
  · exact PEqualNP.Outside.L_meta_8625 _ (by decide)
  · exact PEqualNP.Outside.L_meta_8625 _ (by decide)
  · exact PEqualNP.Outside.L_meta_8625 _ (by decide)
  · exact PEqualNP.Outside.L_meta_8625 _ (by decide)
  · exact PEqualNP.Outside.L_meta_8625 _ (by decide)
  · exact PEqualNP.Outside.L_meta_8625 _ (by decide)
  · exact PEqualNP.Outside.L_meta_8625 _ (by decide)
  · exact PEqualNP.Outside.L_meta_8625 _ (by decide)
  · exact PEqualNP.Outside.L_meta_8625 _ (by decide)
  · exact PEqualNP.Outside.L_meta_8625 _ (by decide)
  · exact PEqualNP.Outside.L_meta_8627 _ (by decide)
  · exact PEqualNP.Outside.L_meta_8627 _ (by decide)
  · exact PEqualNP.Outside.L_meta_8627 _ (by decide)
  · exact PEqualNP.Outside.L_meta_8627 _ (by decide)
  · exact PEqualNP.Outside.L_meta_8627 _ (by decide)
  · exact PEqualNP.Outside.L_meta_8627 _ (by decide)
  · exact PEqualNP.Outside.L_meta_8627 _ (by decide)
  · exact PEqualNP.Outside.L_meta_8627 _ (by decide)
  · exact PEqualNP.Outside.L_meta_8627 _ (by decide)
  · exact PEqualNP.Outside.L_meta_8627 _ (by decide)
  · exact PEqualNP.Outside.L_meta_8629 _ (by decide)
  · exact PEqualNP.Outside.L_meta_8629 _ (by decide)
  · exact PEqualNP.Outside.L_meta_8629 _ (by decide)
  · exact PEqualNP.Outside.L_meta_8629 _ (by decide)
  · exact PEqualNP.Outside.L_meta_8629 _ (by decide)
  · exact PEqualNP.Outside.L_meta_8629 _ (by decide)
  · exact PEqualNP.Outside.L_meta_8463
  · exact PEqualNP.Outside.L_meta_8465
  · exact PEqualNP.Outside.L_meta_8467
