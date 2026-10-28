import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8088 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8088 = true := by
  decide +kernel

theorem tot8088 : totK PA10K2 A10K2.t8088 = [0, 0, 0, 584963438364, 1875135016589, 1719455314270, 575234679722, 58702232814, 0, 0] := by
  decide +kernel

theorem rows8089 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8089 = true := by
  decide +kernel

theorem tot8089 : totK PA10K2 A10K2.t8089 = [0, 0, 0, 189661237311, 1348850991710, 2335906420426, 948532525713, 65094464785, 0, 0] := by
  decide +kernel

theorem rows8090 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8090 = true := by
  decide +kernel

theorem tot8090 : totK PA10K2 A10K2.t8090 = [0, 0, 0, 611103909717, 2016848744473, 1876668429504, 475489485383, 18846688044, 0, 0] := by
  decide +kernel

theorem rows8091 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8091 = true := by
  decide +kernel

theorem tot8091 : totK PA10K2 A10K2.t8091 = [0, 0, 0, 0, 709656064015, 2276713403190, 1797054151369, 296189455354, 6962742351, 0] := by
  decide +kernel

end QECKChecks.A10K2
