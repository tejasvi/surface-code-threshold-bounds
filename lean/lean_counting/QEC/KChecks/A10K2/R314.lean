import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1256 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1256 = true := by
  decide +kernel

theorem tot1256 : totK PA10K2 A10K2.t1256 = [0, 0, 315590801309, 1214092476652, 1781754074207, 1102459938297, 219157925173, 6354482628, 0, 0] := by
  decide +kernel

theorem rows1257 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1257 = true := by
  decide +kernel

theorem tot1257 : totK PA10K2 A10K2.t1257 = [0, 0, 439912506237, 1749305678131, 2018274588392, 569663979175, 32040661968, 0, 0, 0] := by
  decide +kernel

theorem rows1258 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1258 = true := by
  decide +kernel

theorem tot1258 : totK PA10K2 A10K2.t1258 = [0, 0, 86044556310, 849971728803, 1971780492747, 1484902714109, 350976397785, 25371180993, 0, 0] := by
  decide +kernel

theorem rows1259 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1259 = true := by
  decide +kernel

theorem tot1259 : totK PA10K2 A10K2.t1259 = [0, 0, 212862030042, 1046540038621, 1945563594585, 1339330996254, 217000206902, 5447185874, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
