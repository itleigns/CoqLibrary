all:  Tools/BasicTools.vo BasicProperty/NatProperty.vo BasicProperty/MappingProperty.vo Tools/MyProd.vo Tools/MySum.vo BasicNotation/Parity.vo BasicNotation/Permutation.vo LibraryExtension/DatatypesExtension.vo LibraryExtension/EnsemblesExtension.vo MyAlgebraicStructure/MyField.vo MyAlgebraicStructure/MyVectorSpace.vo LinearAlgebra/SenkeiDaisuunoSekai/SenkeiDaisuunoSekai1.vo LinearAlgebra/Matrix.vo Topology/ShuugouIsouNyuumonn/ShuugouIsouNyuumonn1.vo Topology/ShuugouIsouNyuumonn/ShuugouIsouNyuumonn1AC.vo Analysis/KaisekiNyuumonn/KaisekiNyuumonn1_1.vo Analysis/KaisekiNyuumonn/KaisekiNyuumonn1_2.vo Analysis/KaisekiNyuumonn/KaisekiNyuumonn2.vo Topology/ShuugouIsouNyuumonn/ShuugouIsouNyuumonn2.vo Topology/ShuugouIsouNyuumonn/ShuugouIsouNyuumonn2AC.vo

Tools/BasicTools.vo: Tools/BasicTools.v
	coqc -Q Tools Tools Tools/BasicTools.v

BasicProperty/NatProperty.vo: BasicProperty/NatProperty.v
	coqc -Q BasicProperty BasicProperty BasicProperty/NatProperty.v

BasicProperty/MappingProperty.vo: BasicProperty/MappingProperty.v
	coqc -Q BasicProperty BasicProperty BasicProperty/MappingProperty.v

Tools/MyProd.vo: Tools/MyProd.v
	coqc -Q Tools Tools Tools/MyProd.v

Tools/MySum.vo: Tools/MySum.v
	coqc -Q Tools Tools Tools/MySum.v

BasicNotation/Parity.vo: BasicNotation/Parity.v Tools/MySum.vo
	coqc -Q BasicNotation BasicNotation BasicNotation/Parity.v

BasicNotation/Permutation.vo: BasicNotation/Permutation.v BasicNotation/Parity.vo Tools/MySum.vo
	coqc -Q BasicNotation BasicNotation BasicNotation/Permutation.v

LibraryExtension/DatatypesExtension.vo: LibraryExtension/DatatypesExtension.v
	coqc -Q LibraryExtension LibraryExtension LibraryExtension/DatatypesExtension.v

LibraryExtension/EnsemblesExtension.vo: LibraryExtension/EnsemblesExtension.v
	coqc -Q LibraryExtension LibraryExtension LibraryExtension/EnsemblesExtension.v

MyAlgebraicStructure/MyField.vo: MyAlgebraicStructure/MyField.v BasicProperty/NatProperty.vo
	coqc -Q MyAlgebraicStructure MyAlgebraicStructure MyAlgebraicStructure/MyField.v

MyAlgebraicStructure/MyVectorSpace.vo: MyAlgebraicStructure/MyVectorSpace.v MyAlgebraicStructure/MyField.vo BasicProperty/MappingProperty.v
	coqc -Q MyAlgebraicStructure MyAlgebraicStructure MyAlgebraicStructure/MyVectorSpace.v

LinearAlgebra/SenkeiDaisuunoSekai/SenkeiDaisuunoSekai1.vo: MyAlgebraicStructure/MyField.v MyAlgebraicStructure/MyVectorSpace.v BasicProperty/MappingProperty.v BasicProperty/NatProperty.v Tools/MySum.v Tools/BasicTools.v LibraryExtension/DatatypesExtension.v LibraryExtension/EnsemblesExtension.v
	coqc -Q LinearAlgebra/SenkeiDaisuunoSekai LinearAlgebra.SenkeiDaisuunoSekai LinearAlgebra/SenkeiDaisuunoSekai/SenkeiDaisuunoSekai1.v

LinearAlgebra/Matrix.vo: LinearAlgebra/Matrix.v MyAlgebraicStructure/MyField.vo MyAlgebraicStructure/MyVectorSpace.vo Tools/MySum.vo Tools/MyProd.vo
	coqc -Q LinearAlgebra LinearAlgebra LinearAlgebra/Matrix.v

Topology/ShuugouIsouNyuumonn/ShuugouIsouNyuumonn1.vo: Topology/ShuugouIsouNyuumonn/ShuugouIsouNyuumonn1.v Tools/MySum.vo BasicProperty/MappingProperty.vo LibraryExtension/EnsemblesExtension.vo
	coqc -Q Topology/ShuugouIsouNyuumonn Topology.ShuugouIsouNyuumonn Topology/ShuugouIsouNyuumonn/ShuugouIsouNyuumonn1.v

Topology/ShuugouIsouNyuumonn/ShuugouIsouNyuumonn1AC.vo: Topology/ShuugouIsouNyuumonn/ShuugouIsouNyuumonn1AC.v Topology/ShuugouIsouNyuumonn/ShuugouIsouNyuumonn1.vo BasicProperty/MappingProperty.vo
	coqc -Q Topology/ShuugouIsouNyuumonn Topology.ShuugouIsouNyuumonn Topology/ShuugouIsouNyuumonn/ShuugouIsouNyuumonn1AC.v

Analysis/KaisekiNyuumonn/KaisekiNyuumonn1_1.vo: Analysis/KaisekiNyuumonn/KaisekiNyuumonn1_1.v
	coqc -Q Analysis/KaisekiNyuumonn Analysis.KaisekiNyuumonn Analysis/KaisekiNyuumonn/KaisekiNyuumonn1_1.v

Analysis/KaisekiNyuumonn/KaisekiNyuumonn1_2.vo: Analysis/KaisekiNyuumonn/KaisekiNyuumonn1_2.v Analysis/KaisekiNyuumonn/KaisekiNyuumonn1_1.vo MyAlgebraicStructure/MyField.vo MyAlgebraicStructure/MyVectorSpace.vo Tools/MySum.vo
	coqc -Q Analysis/KaisekiNyuumonn Analysis.KaisekiNyuumonn Analysis/KaisekiNyuumonn/KaisekiNyuumonn1_2.v

Analysis/KaisekiNyuumonn/KaisekiNyuumonn2.vo: Analysis/KaisekiNyuumonn/KaisekiNyuumonn2.v BasicProperty/MappingProperty.vo MyAlgebraicStructure/MyField.vo MyAlgebraicStructure/MyVectorSpace.vo Tools/MySum.vo Analysis/KaisekiNyuumonn/KaisekiNyuumonn1_1.vo Analysis/KaisekiNyuumonn/KaisekiNyuumonn1_2.vo
	coqc -Q Analysis/KaisekiNyuumonn Analysis.KaisekiNyuumonn Analysis/KaisekiNyuumonn/KaisekiNyuumonn2.v

Topology/ShuugouIsouNyuumonn/ShuugouIsouNyuumonn2.vo: Topology/ShuugouIsouNyuumonn/ShuugouIsouNyuumonn2.v BasicProperty/MappingProperty.vo LibraryExtension/EnsemblesExtension.vo Topology/ShuugouIsouNyuumonn/ShuugouIsouNyuumonn1.vo LibraryExtension/DatatypesExtension.vo Analysis/KaisekiNyuumonn/KaisekiNyuumonn1_1.vo BasicProperty/NatProperty.vo
	coqc -Q Topology/ShuugouIsouNyuumonn Topology.ShuugouIsouNyuumonn Topology/ShuugouIsouNyuumonn/ShuugouIsouNyuumonn2.v

Topology/ShuugouIsouNyuumonn/ShuugouIsouNyuumonn2AC.vo: Topology/ShuugouIsouNyuumonn/ShuugouIsouNyuumonn2AC.v Tools/BasicTools.vo BasicProperty/MappingProperty.vo  LibraryExtension/DatatypesExtension.vo Topology/ShuugouIsouNyuumonn/ShuugouIsouNyuumonn1.vo Topology/ShuugouIsouNyuumonn/ShuugouIsouNyuumonn1AC.vo Topology/ShuugouIsouNyuumonn/ShuugouIsouNyuumonn2.vo 
	coqc -Q Topology/ShuugouIsouNyuumonn Topology.ShuugouIsouNyuumonn Topology/ShuugouIsouNyuumonn/ShuugouIsouNyuumonn2AC.v

clean:
	find . -type f | grep -E "(.*\.vo)|(.*\.glob)|(.*\.aux)" - | xargs rm