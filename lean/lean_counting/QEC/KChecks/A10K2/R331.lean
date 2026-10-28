import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1324 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1324 = true := by
  decide +kernel

theorem tot1324 : totK PA10K2 A10K2.t1324 = [0, 0, 291577383370, 1250654730251, 1883892362026, 1209174928894, 211452672216, 5447185874, 0, 0] := by
  decide +kernel

theorem rows1325 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1325 = true := by
  decide +kernel

theorem tot1325 : totK PA10K2 A10K2.t1325 = [0, 0, 263367341472, 1447407982250, 2167148638158, 797803460475, 58805274416, 0, 0, 0] := by
  decide +kernel

theorem rows1326 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1326 = true := by
  decide +kernel

theorem tot1326 : totK PA10K2 A10K2.t1326 = [0, 0, 330160462837, 1278220068325, 1879223324424, 1035288081670, 165562159548, 5705019915, 0, 0] := by
  decide +kernel

theorem rows1327 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1327 = true := by
  decide +kernel

theorem tot1327 : totK PA10K2 A10K2.t1327 = [0, 0, 484105024276, 1874863757559, 2111914052302, 656750575510, 27217828541, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
