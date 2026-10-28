import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4104 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4104 = true := by
  decide +kernel

theorem tot4104 : totK PD2M8K2 D2M8K2.t4104 = [0, 177316820630, 461793865268, 249648647095, 23276880172, 0, 0, 0] := by
  decide +kernel

theorem rows4105 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4105 = true := by
  decide +kernel

theorem tot4105 : totK PD2M8K2 D2M8K2.t4105 = [0, 179483918505, 460993963294, 247422978836, 16990428665, 0, 0, 0] := by
  decide +kernel

theorem rows4106 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4106 = true := by
  decide +kernel

theorem tot4106 : totK PD2M8K2 D2M8K2.t4106 = [0, 0, 304030030166, 500554150283, 87856599920, 1096505104, 0, 0] := by
  decide +kernel

theorem rows4107 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4107 = true := by
  decide +kernel

theorem tot4107 : totK PD2M8K2 D2M8K2.t4107 = [0, 77035357472, 317421683771, 385277630386, 107475389867, 3884009855, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
