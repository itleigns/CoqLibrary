all: KaisekiNyuumonn1.vo Matrix.vo MyField.vo MyVectorSpace.vo MySum.vo NatProperty.vo MappingProperty.vo BasicTools.vo DatatypesExtension.vo EnsemblesExtension.vo

KaisekiNyuumonn1.vo: Analysis/KaisekiNyuumonn/KaisekiNyuumonn1.v MyField.vo MyVectorSpace.vo MySum.vo
	coqc -Q Analysis/KaisekiNyuumonn Analysis.KaisekiNyuumonn Analysis/KaisekiNyuumonn/KaisekiNyuumonn1.v

Matrix.vo: LinearAlgebra/Matrix.v MyField.vo MyVectorSpace.vo MySum.vo
	coqc -Q LinearAlgebra LinearAlgebra LinearAlgebra/Matrix.v

MyField.vo: MyAlgebraicStructure/MyField.v NatProperty.vo
	coqc -Q MyAlgebraicStructure MyAlgebraicStructure MyAlgebraicStructure/MyField.v

MyVectorSpace.vo: MyAlgebraicStructure/MyVectorSpace.v MyField.vo
	coqc -Q MyAlgebraicStructure MyAlgebraicStructure MyAlgebraicStructure/MyVectorSpace.v

BasicTools.vo: Tools/BasicTools.v
	coqc -Q Tools Tools Tools/BasicTools.v

MySum.vo: Tools/MySum.v
	coqc -Q Tools Tools Tools/MySum.v

NatProperty.vo: BasicProperty/NatProperty.v
	coqc -Q BasicProperty BasicProperty BasicProperty/NatProperty.v

MappingProperty.vo: BasicProperty/MappingProperty.v
	coqc -Q BasicProperty BasicProperty BasicProperty/MappingProperty.v

DatatypesExtension.vo: LibraryExtension/DatatypesExtension.v
	coqc -Q LibraryExtension LibraryExtension LibraryExtension/DatatypesExtension.v

Ensembles.vo: LibraryExtension/EnsemblesExtension.v
	coqc -Q LibraryExtension LibraryExtension LibraryExtension/EnsemblesExtension.v

clean:
	find . -type f | grep -E "(.*\.vo)|(.*\.glob)|(.*\.aux)" - | xargs rm