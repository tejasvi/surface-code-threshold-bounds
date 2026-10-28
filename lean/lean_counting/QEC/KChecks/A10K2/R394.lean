import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1576 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1576 = true := by
  decide +kernel

theorem tot1576 : totK PA10K2 A10K2.t1576 = [0, 0, 107692589913, 1125523660491, 2229134636078, 1041333313714, 92227200439, 0, 0, 0] := by
  decide +kernel

theorem rows1577 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1577 = true := by
  decide +kernel

theorem tot1577 : totK PA10K2 A10K2.t1577 = [0, 0, 505396897191, 1655926042369, 1664550746029, 698555610133, 134777216809, 6034215561, 0, 0] := by
  decide +kernel

theorem rows1578 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1578 = true := by
  decide +kernel

theorem tot1578 : totK PA10K2 A10K2.t1578 = [0, 0, 303792748393, 1475316864121, 2069924133637, 727284174521, 52620687920, 0, 0, 0] := by
  decide +kernel

theorem rows1579 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1579 = true := by
  decide +kernel

theorem tot1579 : totK PA10K2 A10K2.t1579 = [0, 0, 0, 710061639965, 2105943139925, 1501352515180, 257388413100, 6354482628, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
