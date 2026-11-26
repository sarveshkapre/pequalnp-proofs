import PEqualNP.ThreeGateGain.FiniteV05P006

namespace GainFinite.F5
open GainFinite
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem n560 : fastVisit (leafCols 5 bank) [9,4] ⟨518144,[59392,327680]⟩ b9 = true := join_live n543 n559

theorem n561 : fastVisit (leafCols 5 bank) [4] ⟨458752,[458752]⟩ b8 = true := join_live n527 n560

theorem n562 : fastVisit (leafFrame 5 [8,4] ⟨520192,[61440,196608]⟩) [] ⟨0,[]⟩ b49 = true := by decide +kernel

theorem n563 : fastVisit (leafFrame 5 [8,4] ⟨520192,[61440,196608]⟩) [1] ⟨299008,[299008]⟩ b49 = true := by decide +kernel

theorem n564 : fastVisit (leafFrame 5 [8,4] ⟨520192,[61440,196608]⟩) [] ⟨0,[]⟩ b48 = true := join_live n562 n563

theorem n565 : fastVisit (leafCols 5 bank) [8,4] ⟨520192,[61440,196608]⟩ b18 = true := enterColumns 5 bank [8,4] ⟨520192,[61440,196608]⟩ b18 b48 (by decide +kernel) (by decide +kernel) n564

theorem n566 : fastVisit (leafCols 5 bank) [18,8,4] ⟨522618,[2426,4096,65536]⟩ b18 = true := by decide +kernel

theorem n567 : fastVisit (leafCols 5 bank) [8,4] ⟨520192,[61440,196608]⟩ b17 = true := join_live n565 n566

theorem n568 : fastVisit (leafCols 5 bank) [8,4] ⟨520192,[61440,196608]⟩ b16 = true := join_dead n567 (by decide +kernel)

theorem n569 : fastVisit (leafCols 5 bank) [16,8,4] ⟨520312,[120,4096,196608]⟩ b16 = true := by decide +kernel

theorem n570 : fastVisit (leafCols 5 bank) [8,4] ⟨520192,[61440,196608]⟩ b15 = true := join_live n568 n569

theorem n571 : fastVisit (leafCols 5 bank) [8,4] ⟨520192,[61440,196608]⟩ b14 = true := join_dead n570 (by decide +kernel)

theorem n572 : fastVisit (leafCols 5 bank) [8,4] ⟨520192,[61440,196608]⟩ b13 = true := join_dead n571 (by decide +kernel)

theorem n573 : fastVisit (leafCols 5 bank) [8,4] ⟨520192,[61440,196608]⟩ b12 = true := join_dead n572 (by decide +kernel)

theorem n574 : fastVisit (leafCols 5 bank) [12,8,4] ⟨522538,[2346,45056,65536]⟩ b12 = true := by decide +kernel

theorem n575 : fastVisit (leafCols 5 bank) [8,4] ⟨520192,[61440,196608]⟩ b11 = true := join_live n573 n574

theorem n576 : fastVisit (leafCols 5 bank) [11,8,4] ⟨520780,[588,24576,196608]⟩ b11 = true := by decide +kernel

theorem n577 : fastVisit (leafCols 5 bank) [8,4] ⟨520192,[61440,196608]⟩ b10 = true := join_live n575 n576

theorem n578 : fastVisit (leafFrame 5 [10,8,4] ⟨520200,[8,61440,196608]⟩) [] ⟨0,[]⟩ b52 = true := by decide +kernel

theorem n579 : fastVisit (leafFrame 5 [10,8,4] ⟨520200,[8,61440,196608]⟩) [2] ⟨149504,[149504]⟩ b52 = true := by decide +kernel

theorem n580 : fastVisit (leafFrame 5 [10,8,4] ⟨520200,[8,61440,196608]⟩) [] ⟨0,[]⟩ b51 = true := join_live n578 n579

theorem n581 : fastVisit (leafFrame 5 [10,8,4] ⟨520200,[8,61440,196608]⟩) [1] ⟨299008,[299008]⟩ b51 = true := by decide +kernel

theorem n582 : fastVisit (leafFrame 5 [10,8,4] ⟨520200,[8,61440,196608]⟩) [] ⟨0,[]⟩ b50 = true := join_live n580 n581

theorem n583 : fastVisit (leafCols 5 bank) [10,8,4] ⟨520200,[8,61440,196608]⟩ b18 = true := enterColumns 5 bank [10,8,4] ⟨520200,[8,61440,196608]⟩ b18 b50 (by decide +kernel) (by decide +kernel) n582

theorem n584 : fastVisit (leafCols 5 bank) [10,8,4] ⟨520200,[8,61440,196608]⟩ b17 = true := join_dead n583 (by decide +kernel)

theorem n585 : fastVisit (leafCols 5 bank) [10,8,4] ⟨520200,[8,61440,196608]⟩ b16 = true := join_dead n584 (by decide +kernel)

theorem n586 : fastVisit (leafCols 5 bank) [10,8,4] ⟨520200,[8,61440,196608]⟩ b15 = true := join_dead n585 (by decide +kernel)

theorem n587 : fastVisit (leafCols 5 bank) [10,8,4] ⟨520200,[8,61440,196608]⟩ b14 = true := join_dead n586 (by decide +kernel)

theorem n588 : fastVisit (leafCols 5 bank) [10,8,4] ⟨520200,[8,61440,196608]⟩ b13 = true := join_dead n587 (by decide +kernel)

theorem n589 : fastVisit (leafCols 5 bank) [10,8,4] ⟨520200,[8,61440,196608]⟩ b12 = true := join_dead n588 (by decide +kernel)

theorem n590 : fastVisit (leafCols 5 bank) [10,8,4] ⟨520200,[8,61440,196608]⟩ b11 = true := join_dead n589 (by decide +kernel)

theorem n591 : fastVisit (leafCols 5 bank) [10,8,4] ⟨520200,[8,61440,196608]⟩ b10 = true := join_dead n590 (by decide +kernel)

theorem n592 : fastVisit (leafCols 5 bank) [8,4] ⟨520192,[61440,196608]⟩ b9 = true := join_live n577 n591

theorem n593 : fastVisit (leafFrame 5 [9,8,4] ⟨522240,[2048,4096,65536]⟩) [] ⟨0,[]⟩ b60 = true := by decide +kernel

theorem n594 : fastVisit (leafFrame 5 [9,8,4] ⟨522240,[2048,4096,65536]⟩) [2] ⟨149504,[149504]⟩ b60 = true := by decide +kernel

theorem n595 : fastVisit (leafFrame 5 [9,8,4] ⟨522240,[2048,4096,65536]⟩) [] ⟨0,[]⟩ b59 = true := join_live n593 n594

theorem n596 : fastVisit (leafFrame 5 [9,8,4] ⟨522240,[2048,4096,65536]⟩) [1] ⟨299008,[299008]⟩ b59 = true := by decide +kernel

theorem n597 : fastVisit (leafFrame 5 [9,8,4] ⟨522240,[2048,4096,65536]⟩) [] ⟨0,[]⟩ b58 = true := join_live n595 n596

theorem n598 : fastVisit (leafCols 5 bank) [9,8,4] ⟨522240,[2048,4096,65536]⟩ b18 = true := enterColumns 5 bank [9,8,4] ⟨522240,[2048,4096,65536]⟩ b18 b58 (by decide +kernel) (by decide +kernel) n597

theorem n599 : fastVisit (leafCols 5 bank) [9,8,4] ⟨522240,[2048,4096,65536]⟩ b17 = true := join_dead n598 (by decide +kernel)

theorem n600 : fastVisit (leafCols 5 bank) [9,8,4] ⟨522240,[2048,4096,65536]⟩ b16 = true := join_dead n599 (by decide +kernel)

theorem n601 : fastVisit (leafCols 5 bank) [16,9,8,4] ⟨522360,[120,2048,4096,65536]⟩ b16 = true := by decide +kernel

theorem n602 : fastVisit (leafCols 5 bank) [9,8,4] ⟨522240,[2048,4096,65536]⟩ b15 = true := join_live n600 n601

theorem n603 : fastVisit (leafCols 5 bank) [9,8,4] ⟨522240,[2048,4096,65536]⟩ b14 = true := join_dead n602 (by decide +kernel)

theorem n604 : fastVisit (leafCols 5 bank) [9,8,4] ⟨522240,[2048,4096,65536]⟩ b13 = true := join_dead n603 (by decide +kernel)

theorem n605 : fastVisit (leafCols 5 bank) [9,8,4] ⟨522240,[2048,4096,65536]⟩ b12 = true := join_dead n604 (by decide +kernel)

theorem n606 : fastVisit (leafCols 5 bank) [9,8,4] ⟨522240,[2048,4096,65536]⟩ b11 = true := join_dead n605 (by decide +kernel)

theorem n607 : fastVisit (leafCols 5 bank) [9,8,4] ⟨522240,[2048,4096,65536]⟩ b10 = true := join_dead n606 (by decide +kernel)

theorem n608 : fastVisit (leafFrame 5 [10,9,8,4] ⟨522248,[8,2048,4096,65536]⟩) [] ⟨0,[]⟩ b62 = true := by decide +kernel

theorem n609 : fastVisit (leafFrame 5 [10,9,8,4] ⟨522248,[8,2048,4096,65536]⟩) [5] ⟨495616,[495616]⟩ b62 = true := by decide +kernel

theorem n610 : fastVisit (leafFrame 5 [10,9,8,4] ⟨522248,[8,2048,4096,65536]⟩) [] ⟨0,[]⟩ b61 = true := join_live n608 n609

theorem n611 : fastVisit (leafFrame 5 [10,9,8,4] ⟨522248,[8,2048,4096,65536]⟩) [4] ⟨458752,[458752]⟩ b61 = true := by decide +kernel

theorem n612 : fastVisit (leafFrame 5 [10,9,8,4] ⟨522248,[8,2048,4096,65536]⟩) [] ⟨0,[]⟩ b45 = true := join_live n610 n611

theorem n613 : fastVisit (leafFrame 5 [10,9,8,4] ⟨522248,[8,2048,4096,65536]⟩) [2] ⟨149504,[149504]⟩ b45 = true := by decide +kernel

theorem n614 : fastVisit (leafFrame 5 [10,9,8,4] ⟨522248,[8,2048,4096,65536]⟩) [] ⟨0,[]⟩ b44 = true := join_live n612 n613

theorem n615 : fastVisit (leafFrame 5 [10,9,8,4] ⟨522248,[8,2048,4096,65536]⟩) [1] ⟨299008,[299008]⟩ b45 = true := by decide +kernel

theorem n616 : fastVisit (leafFrame 5 [10,9,8,4] ⟨522248,[8,2048,4096,65536]⟩) [2,1] ⟨448512,[149504,299008]⟩ b45 = true := by decide +kernel

theorem n617 : fastVisit (leafFrame 5 [10,9,8,4] ⟨522248,[8,2048,4096,65536]⟩) [1] ⟨299008,[299008]⟩ b44 = true := join_live n615 n616

theorem n618 : fastVisit (leafFrame 5 [10,9,8,4] ⟨522248,[8,2048,4096,65536]⟩) [] ⟨0,[]⟩ b43 = true := join_live n614 n617

theorem n619 : fastVisit (leafCols 5 bank) [10,9,8,4] ⟨522248,[8,2048,4096,65536]⟩ b18 = true := enterColumns 5 bank [10,9,8,4] ⟨522248,[8,2048,4096,65536]⟩ b18 b43 (by decide +kernel) (by decide +kernel) n618

theorem n620 : fastVisit (leafCols 5 bank) [10,9,8,4] ⟨522248,[8,2048,4096,65536]⟩ b17 = true := join_dead n619 (by decide +kernel)

theorem n621 : fastVisit (leafCols 5 bank) [10,9,8,4] ⟨522248,[8,2048,4096,65536]⟩ b16 = true := join_dead n620 (by decide +kernel)

theorem n622 : fastVisit (leafCols 5 bank) [10,9,8,4] ⟨522248,[8,2048,4096,65536]⟩ b15 = true := join_dead n621 (by decide +kernel)

theorem n623 : fastVisit (leafCols 5 bank) [10,9,8,4] ⟨522248,[8,2048,4096,65536]⟩ b14 = true := join_dead n622 (by decide +kernel)

theorem n624 : fastVisit (leafCols 5 bank) [10,9,8,4] ⟨522248,[8,2048,4096,65536]⟩ b13 = true := join_dead n623 (by decide +kernel)

theorem n625 : fastVisit (leafCols 5 bank) [10,9,8,4] ⟨522248,[8,2048,4096,65536]⟩ b12 = true := join_dead n624 (by decide +kernel)

theorem n626 : fastVisit (leafCols 5 bank) [10,9,8,4] ⟨522248,[8,2048,4096,65536]⟩ b11 = true := join_dead n625 (by decide +kernel)

theorem n627 : fastVisit (leafCols 5 bank) [10,9,8,4] ⟨522248,[8,2048,4096,65536]⟩ b10 = true := join_dead n626 (by decide +kernel)

theorem n628 : fastVisit (leafCols 5 bank) [9,8,4] ⟨522240,[2048,4096,65536]⟩ b9 = true := join_live n607 n627

theorem n629 : fastVisit (leafCols 5 bank) [8,4] ⟨520192,[61440,196608]⟩ b8 = true := join_live n592 n628

theorem n630 : fastVisit (leafCols 5 bank) [4] ⟨458752,[458752]⟩ b7 = true := join_live n561 n629

theorem n631 : fastVisit (leafFrame 5 [7,4] ⟨516096,[57344,458752]⟩) [] ⟨0,[]⟩ b70 = true := by decide +kernel

theorem n632 : fastVisit (leafFrame 5 [7,4] ⟨516096,[57344,458752]⟩) [1] ⟨299008,[299008]⟩ b70 = true := by decide +kernel

theorem n633 : fastVisit (leafFrame 5 [7,4] ⟨516096,[57344,458752]⟩) [] ⟨0,[]⟩ b69 = true := join_live n631 n632

theorem n634 : fastVisit (leafCols 5 bank) [7,4] ⟨516096,[57344,458752]⟩ b18 = true := enterColumns 5 bank [7,4] ⟨516096,[57344,458752]⟩ b18 b69 (by decide +kernel) (by decide +kernel) n633

theorem n635 : fastVisit (leafCols 5 bank) [7,4] ⟨516096,[57344,458752]⟩ b17 = true := join_dead n634 (by decide +kernel)

theorem n636 : fastVisit (leafCols 5 bank) [7,4] ⟨516096,[57344,458752]⟩ b16 = true := join_dead n635 (by decide +kernel)

theorem n637 : fastVisit (leafCols 5 bank) [7,4] ⟨516096,[57344,458752]⟩ b15 = true := join_dead n636 (by decide +kernel)

theorem n638 : fastVisit (leafCols 5 bank) [7,4] ⟨516096,[57344,458752]⟩ b14 = true := join_dead n637 (by decide +kernel)

theorem n639 : fastVisit (leafCols 5 bank) [7,4] ⟨516096,[57344,458752]⟩ b13 = true := join_dead n638 (by decide +kernel)

end GainFinite.F5
