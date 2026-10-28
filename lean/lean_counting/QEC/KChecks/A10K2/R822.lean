import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3288 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3288 = true := by
  decide +kernel

theorem tot3288 : totK PA10K2 A10K2.t3288 = [0, 0, 468566045184, 1809760246891, 2032135748270, 544967436127, 18754734689, 0, 0, 0] := by
  decide +kernel

theorem rows3289 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3289 = true := by
  decide +kernel

theorem tot3289 : totK PA10K2 A10K2.t3289 = [0, 0, 511375925591, 1771103313628, 1747496946383, 485263870957, 44363554315, 0, 0, 0] := by
  decide +kernel

theorem rows3290 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3290 = true := by
  decide +kernel

theorem tot3290 : totK PA10K2 A10K2.t3290 = [0, 0, 306484836393, 1560896737144, 2094397093802, 651975842798, 38148714322, 0, 0, 0] := by
  decide +kernel

theorem rows3291 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3291 = true := by
  decide +kernel

theorem tot3291 : totK PA10K2 A10K2.t3291 = [0, 0, 265936948311, 1083973930142, 1868237983461, 1188354920245, 233528391130, 6354482628, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
