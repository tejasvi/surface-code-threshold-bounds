import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1300 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1300 = true := by
  decide +kernel

theorem tot1300 : totK PA10K2 A10K2.t1300 = [0, 0, 466772010805, 1850291140959, 2117147076150, 665189521861, 30118920131, 0, 0, 0] := by
  decide +kernel

theorem rows1301 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1301 = true := by
  decide +kernel

theorem tot1301 : totK PA10K2 A10K2.t1301 = [0, 0, 592988321650, 1980923277712, 1915053062495, 559719465087, 52486959823, 0, 0, 0] := by
  decide +kernel

theorem rows1302 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1302 = true := by
  decide +kernel

theorem tot1302 : totK PA10K2 A10K2.t1302 = [0, 0, 0, 778821495673, 2280871406794, 1634529931446, 271636716920, 8047840951, 0, 0] := by
  decide +kernel

theorem rows1303 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1303 = true := by
  decide +kernel

theorem tot1303 : totK PA10K2 A10K2.t1303 = [0, 0, 585758096377, 2003981577447, 2011827208426, 519577931958, 31474416616, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
