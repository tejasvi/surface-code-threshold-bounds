import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4044 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4044 = true := by
  decide +kernel

theorem tot4044 : totK PD2M8K2 D2M8K2.t4044 = [0, 0, 0, 276482298333, 491027987272, 123544803444, 4009909289, 0] := by
  decide +kernel

theorem rows4045 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4045 = true := by
  decide +kernel

theorem tot4045 : totK PD2M8K2 D2M8K2.t4045 = [0, 0, 94106722254, 348826887545, 374247104561, 77569876963, 1149959346, 0] := by
  decide +kernel

theorem rows4046 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4046 = true := by
  decide +kernel

theorem tot4046 : totK PD2M8K2 D2M8K2.t4046 = [0, 0, 166046717687, 442931775367, 279090490410, 30183372270, 0, 0] := by
  decide +kernel

theorem rows4047 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4047 = true := by
  decide +kernel

theorem tot4047 : totK PD2M8K2 D2M8K2.t4047 = [0, 0, 157318236314, 465412475346, 263479412435, 14917056564, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
