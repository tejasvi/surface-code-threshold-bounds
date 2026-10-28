import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2944 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2944 = true := by
  decide +kernel

theorem tot2944 : totK PA10K2 A10K2.t2944 = [0, 297281370121, 1407935340204, 2171292484601, 1110537542132, 111872611049, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2945 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2945 = true := by
  decide +kernel

theorem tot2945 : totK PA10K2 A10K2.t2945 = [0, 0, 509066606607, 1824323806874, 1892401448107, 516982774448, 31306924438, 0, 0, 0] := by
  decide +kernel

theorem rows2946 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2946 = true := by
  decide +kernel

theorem tot2946 : totK PA10K2 A10K2.t2946 = [0, 465256280536, 1836591788010, 1978276521805, 568775006787, 32569280177, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2947 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2947 = true := by
  decide +kernel

theorem tot2947 : totK PA10K2 A10K2.t2947 = [0, 214399859331, 1155529607430, 2100675241361, 1243517344924, 196500675959, 6239673734, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
