all: KaisekiNyuumonn1.vo Matrix.vo MyField.vo MyVectorSpace.vo MySum.vo

KaisekiNyuumonn1.vo: Analysis/KaisekiNyuumonn/KaisekiNyuumonn1.v MyField.vo MyVectorSpace.vo MySum.vo
	coqc Analysis/KaisekiNyuumonn/KaisekiNyuumonn1.v

Matrix.vo: LinearAlgebra/Matrix.v MyField.vo MyVectorSpace.vo MySum.vo
	coqc -Q LinearAlgebra LinearAlgebra LinearAlgebra/Matrix.v

MyField.vo: MyAlgebraicStructure/MyField.v
	coqc -Q MyAlgebraicStructure MyAlgebraicStructure MyAlgebraicStructure/MyField.v

MyVectorSpace.vo: MyAlgebraicStructure/MyVectorSpace.v MyField.vo
	coqc -Q MyAlgebraicStructure MyAlgebraicStructure MyAlgebraicStructure/MyVectorSpace.v

MySum.vo: Tools/MySum.v
	coqc -Q Tools Tools Tools/MySum.v

clean:
	find . -type f | grep -E "(.*\.vo)|(.*\.glob)|(.*\.aux)" - | xargs rm