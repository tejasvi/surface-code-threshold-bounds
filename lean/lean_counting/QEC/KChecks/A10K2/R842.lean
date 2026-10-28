import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3368 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3368 = true := by
  decide +kernel

theorem tot3368 : totK PA10K2 A10K2.t3368 = [0, 0, 80046160963, 1072442486573, 2258809953615, 1147082589462, 105076043682, 0, 0, 0] := by
  decide +kernel

theorem rows3369 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3369 = true := by
  decide +kernel

theorem tot3369 : totK PA10K2 A10K2.t3369 = [0, 0, 495771531347, 1711050914556, 1871529660963, 743825906736, 131645794425, 6239673734, 0, 0] := by
  decide +kernel

theorem rows3370 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3370 = true := by
  decide +kernel

theorem tot3370 : totK PA10K2 A10K2.t3370 = [0, 0, 319364795913, 1486494205761, 2183832916375, 1068204645796, 111349822878, 0, 0, 0] := by
  decide +kernel

theorem rows3371 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3371 = true := by
  decide +kernel

theorem tot3371 : totK PA10K2 A10K2.t3371 = [0, 0, 0, 613592017148, 2100568695059, 1968746494425, 398776235938, 6962742351, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
