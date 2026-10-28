import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10368 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10368 = true := by
  decide +kernel

theorem tot10368 : totK PD2M8K2 D2M8K2.t10368 = [0, 0, 0, 238754774740, 494570879022, 130009564245, 2243379097, 0] := by
  decide +kernel

theorem rows10369 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10369 = true := by
  decide +kernel

theorem tot10369 : totK PD2M8K2 D2M8K2.t10369 = [0, 0, 55388964612, 213365692823, 391824369032, 199212294147, 15126214521, 0] := by
  decide +kernel

theorem rows10370 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10370 = true := by
  decide +kernel

theorem tot10370 : totK PD2M8K2 D2M8K2.t10370 = [0, 0, 206102672691, 482057266476, 195098487557, 6142729504, 0, 0] := by
  decide +kernel

theorem rows10371 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10371 = true := by
  decide +kernel

theorem tot10371 : totK PD2M8K2 D2M8K2.t10371 = [0, 0, 173361319786, 477945415742, 228300947593, 12534051746, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
