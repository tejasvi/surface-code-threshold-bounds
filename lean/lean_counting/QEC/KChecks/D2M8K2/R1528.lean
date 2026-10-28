import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6112 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6112 = true := by
  decide +kernel

theorem tot6112 : totK PD2M8K2 D2M8K2.t6112 = [0, 0, 184902469070, 462624923544, 246781348397, 22205007253, 0, 0] := by
  decide +kernel

theorem rows6113 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6113 = true := by
  decide +kernel

theorem tot6113 : totK PD2M8K2 D2M8K2.t6113 = [0, 0, 161406326445, 433605242636, 270076557000, 17620340621, 0, 0] := by
  decide +kernel

theorem rows6114 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6114 = true := by
  decide +kernel

theorem tot6114 : totK PD2M8K2 D2M8K2.t6114 = [0, 0, 80294694507, 417732312576, 373512198169, 33390985464, 0, 0] := by
  decide +kernel

theorem rows6115 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6115 = true := by
  decide +kernel

theorem tot6115 : totK PD2M8K2 D2M8K2.t6115 = [0, 0, 63589113928, 334377845343, 396706999844, 76769183342, 1323630408, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
