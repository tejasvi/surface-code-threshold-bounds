import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5260 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5260 = true := by
  decide +kernel

theorem tot5260 : totK PD2M8K2 D2M8K2.t5260 = [0, 0, 181574117857, 460017927099, 260443372588, 23032659230, 0, 0] := by
  decide +kernel

theorem rows5261 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5261 = true := by
  decide +kernel

theorem tot5261 : totK PD2M8K2 D2M8K2.t5261 = [0, 0, 166670660977, 460843350484, 258619860714, 14631860856, 0, 0] := by
  decide +kernel

theorem rows5262 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5262 = true := by
  decide +kernel

theorem tot5262 : totK PD2M8K2 D2M8K2.t5262 = [0, 0, 0, 276815159100, 488749873032, 122882805728, 4009909289, 0] := by
  decide +kernel

theorem rows5263 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5263 = true := by
  decide +kernel

theorem tot5263 : totK PD2M8K2 D2M8K2.t5263 = [0, 0, 97229344615, 349687520504, 369787768513, 76119208956, 1149959346, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
