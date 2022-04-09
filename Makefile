all:  BasicTools.vo NatProperty.vo MappingProperty.vo MySum.vo MyProd.vo Parity.vo Permutation.vo DatatypesExtension.vo EnsemblesExtension.vo MyField.vo MyVectorSpace.vo SenkeiDaisuunoSekai1.vo Matrix.vo ShuugouIsouNyuumonn1.vo ShuugouIsouNyuumonn1AC.vo KaisekiNyuumonn1_1.vo　ShuugouIsouNyuumonn2.vo ShuugouIsouNyuumonn2AC.vo KaisekiNyuumonn1_2.vo

BasicTools.vo: Tools/BasicTools.v
	coqc -Q Tools Tools Tools/BasicTools.v

NatProperty.vo: BasicProperty/NatProperty.v
	coqc -Q BasicProperty BasicProperty BasicProperty/NatProperty.v

MappingProperty.vo: BasicProperty/MappingProperty.v
	coqc -Q BasicProperty BasicProperty BasicProperty/MappingProperty.v

MyProd.vo: Tools/MyProd.v
	coqc -Q Tools Tools Tools/MyProd.v

MySum.vo: Tools/MySum.v
	coqc -Q Tools Tools Tools/MySum.v

Parity.vo: BasicNotation/Parity.v MySum.vo
	coqc -Q BasicNotation BasicNotation BasicNotation/Parity.v

Permutation.vo: BasicNotation/Permutation.v Parity.vo MySum.vo
	coqc -Q BasicNotation BasicNotation BasicNotation/Permutation.v

DatatypesExtension.vo: LibraryExtension/DatatypesExtension.v
	coqc -Q LibraryExtension LibraryExtension LibraryExtension/DatatypesExtension.v

EnsemblesExtension.vo: LibraryExtension/EnsemblesExtension.v
	coqc -Q LibraryExtension LibraryExtension LibraryExtension/EnsemblesExtension.v

MyField.vo: MyAlgebraicStructure/MyField.v NatProperty.vo
	coqc -Q MyAlgebraicStructure MyAlgebraicStructure MyAlgebraicStructure/MyField.v

MyVectorSpace.vo: MyAlgebraicStructure/MyVectorSpace.v MyField.vo BasicProperty/MappingProperty.v
	coqc -Q MyAlgebraicStructure MyAlgebraicStructure MyAlgebraicStructure/MyVectorSpace.v

SenkeiDaisuunoSekai1.vo: MyAlgebraicStructure/MyField.v MyAlgebraicStructure/MyVectorSpace.v BasicProperty/MappingProperty.v BasicProperty/NatProperty.v Tools/MySum.v Tools/BasicTools.v LibraryExtension/DatatypesExtension.v LibraryExtension/EnsemblesExtension.v
	coqc -Q LinearAlgebra/SenkeiDaisuunoSekai LinearAlgebra.SenkeiDaisuunoSekai LinearAlgebra/SenkeiDaisuunoSekai/SenkeiDaisuunoSekai1.v

Matrix.vo: LinearAlgebra/Matrix.v MyField.vo MyVectorSpace.vo MySum.vo MyProd.vo
	coqc -Q LinearAlgebra LinearAlgebra LinearAlgebra/Matrix.v

ShuugouIsouNyuumonn1.vo: Topology/ShuugouIsouNyuumonn/ShuugouIsouNyuumonn1.v MySum.vo MappingProperty.vo EnsemblesExtension.vo
	coqc -Q Topology/ShuugouIsouNyuumonn Topology.ShuugouIsouNyuumonn Topology/ShuugouIsouNyuumonn/ShuugouIsouNyuumonn1.v

ShuugouIsouNyuumonn1AC.vo: Topology/ShuugouIsouNyuumonn/ShuugouIsouNyuumonn1AC.v ShuugouIsouNyuumonn1.vo MappingProperty.vo
	coqc -Q Topology/ShuugouIsouNyuumonn Topology.ShuugouIsouNyuumonn Topology/ShuugouIsouNyuumonn/ShuugouIsouNyuumonn1AC.v

KaisekiNyuumonn1_1.vo: Analysis/KaisekiNyuumonn/KaisekiNyuumonn1_1.v
	coqc -Q Analysis/KaisekiNyuumonn Analysis.KaisekiNyuumonn Analysis/KaisekiNyuumonn/KaisekiNyuumonn1_1.v

KaisekiNyuumonn1_2.vo: Analysis/KaisekiNyuumonn/KaisekiNyuumonn1_2.v KaisekiNyuumonn1_1.vo MyField.vo MyVectorSpace.vo MySum.vo
	coqc -Q Analysis/KaisekiNyuumonn Analysis.KaisekiNyuumonn Analysis/KaisekiNyuumonn/KaisekiNyuumonn1_2.v

ShuugouIsouNyuumonn2.vo: Topology/ShuugouIsouNyuumonn/ShuugouIsouNyuumonn2.v MappingProperty.vo EnsemblesExtension.vo ShuugouIsouNyuumonn1.vo DatatypesExtension.vo KaisekiNyuumonn1.vo NatProperty.vo
	coqc -Q Topology/ShuugouIsouNyuumonn Topology.ShuugouIsouNyuumonn Topology/ShuugouIsouNyuumonn/ShuugouIsouNyuumonn2.v

ShuugouIsouNyuumonn2AC.vo: Topology/ShuugouIsouNyuumonn/ShuugouIsouNyuumonn2AC.v BasicTools.vo MappingProperty.vo DatatypesExtension.vo ShuugouIsouNyuumonn1.vo ShuugouIsouNyuumonn1AC.vo ShuugouIsouNyuumonn2.vo 
	coqc -Q Topology/ShuugouIsouNyuumonn Topology.ShuugouIsouNyuumonn Topology/ShuugouIsouNyuumonn/ShuugouIsouNyuumonn2AC.v

clean:
	find . -type f | grep -E "(.*\.vo)|(.*\.glob)|(.*\.aux)" - | xargs rm