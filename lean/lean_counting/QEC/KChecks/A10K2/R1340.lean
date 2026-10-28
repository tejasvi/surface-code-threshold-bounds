import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5360 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5360 = true := by
  decide +kernel

theorem tot5360 : totK PA10K2 A10K2.t5360 = [0, 0, 0, 555169158630, 1970871330942, 1813279449972, 332480757456, 11531959710, 0, 0] := by
  decide +kernel

theorem rows5361 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5361 = true := by
  decide +kernel

theorem tot5361 : totK PA10K2 A10K2.t5361 = [0, 0, 0, 688529754370, 2190072279387, 1902968172932, 357734839202, 11968980090, 0, 0] := by
  decide +kernel

theorem rows5362 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5362 = true := by
  decide +kernel

theorem tot5362 : totK PA10K2 A10K2.t5362 = [0, 0, 474586958601, 1497156873475, 1633199735136, 967359528745, 325386459613, 30751586446, 0, 0] := by
  decide +kernel

theorem rows5363 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5363 = true := by
  decide +kernel

theorem tot5363 : totK PA10K2 A10K2.t5363 = [0, 0, 306042294805, 1532428579332, 2176730193222, 864027875825, 71733655854, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
