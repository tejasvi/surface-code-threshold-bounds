import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6508 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6508 = true := by
  decide +kernel

theorem tot6508 : totK PD2M8K2 D2M8K2.t6508 = [0, 4200607152, 299231610459, 488592627038, 114948261688, 1238673482, 0, 0] := by
  decide +kernel

theorem rows6509 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6509 = true := by
  decide +kernel

theorem tot6509 : totK PD2M8K2 D2M8K2.t6509 = [85882852960, 116305651310, 151977895353, 361043279953, 162343418149, 8063697217, 0, 0] := by
  decide +kernel

theorem rows6510 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6510 = true := by
  decide +kernel

theorem tot6510 : totK PD2M8K2 D2M8K2.t6510 = [157163775052, 468987348537, 246197450338, 14464158903, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6511 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6511 = true := by
  decide +kernel

theorem tot6511 : totK PD2M8K2 D2M8K2.t6511 = [164185697183, 450692910964, 253474267300, 15619378041, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
