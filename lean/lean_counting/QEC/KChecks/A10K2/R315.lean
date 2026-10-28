import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1260 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1260 = true := by
  decide +kernel

theorem tot1260 : totK PA10K2 A10K2.t1260 = [0, 0, 473188973135, 1683770268509, 1880794819614, 587219200106, 37026429097, 0, 0, 0] := by
  decide +kernel

theorem rows1261 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1261 = true := by
  decide +kernel

theorem tot1261 : totK PA10K2 A10K2.t1261 = [0, 0, 73636251830, 1175187012601, 2346687109104, 1023129001482, 71447845990, 0, 0, 0] := by
  decide +kernel

theorem rows1262 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1262 = true := by
  decide +kernel

theorem tot1262 : totK PA10K2 A10K2.t1262 = [0, 0, 403404581151, 1317272064582, 1800082224324, 1068858424586, 191566665508, 6354482628, 0, 0] := by
  decide +kernel

theorem rows1263 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1263 = true := by
  decide +kernel

theorem tot1263 : totK PA10K2 A10K2.t1263 = [0, 0, 186834025656, 1238638631077, 2161972886128, 1247182777720, 196319749999, 6853348008, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
