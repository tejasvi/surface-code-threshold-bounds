import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12372 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12372 = true := by
  decide +kernel

theorem tot12372 : totK PD2M8K2 D2M8K2.t12372 = [0, 0, 188668812066, 480437772441, 193646777125, 9652099503, 0, 0] := by
  decide +kernel

theorem rows12373 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12373 = true := by
  decide +kernel

theorem tot12373 : totK PD2M8K2 D2M8K2.t12373 = [0, 0, 194304437478, 470418158460, 200002262418, 12297602142, 0, 0] := by
  decide +kernel

theorem rows12374 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12374 = true := by
  decide +kernel

theorem tot12374 : totK PD2M8K2 D2M8K2.t12374 = [0, 20021956556, 293056795175, 471468672608, 110580194043, 1369587937, 0, 0] := by
  decide +kernel

theorem rows12375 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12375 = true := by
  decide +kernel

theorem tot12375 : totK PD2M8K2 D2M8K2.t12375 = [0, 168792313441, 444179081878, 279998165066, 29350723805, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
