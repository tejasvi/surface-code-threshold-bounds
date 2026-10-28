import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6080 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6080 = true := by
  decide +kernel

theorem tot6080 : totK PD2M8K2 D2M8K2.t6080 = [0, 0, 199282845287, 479804469006, 207138240662, 9357067284, 0, 0] := by
  decide +kernel

theorem rows6081 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6081 = true := by
  decide +kernel

theorem tot6081 : totK PD2M8K2 D2M8K2.t6081 = [0, 0, 190509912268, 484558328928, 217098729546, 11051716772, 0, 0] := by
  decide +kernel

theorem rows6082 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6082 = true := by
  decide +kernel

theorem tot6082 : totK PD2M8K2 D2M8K2.t6082 = [0, 0, 157164107747, 469952933457, 251968074020, 13668189840, 0, 0] := by
  decide +kernel

theorem rows6083 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6083 = true := by
  decide +kernel

theorem tot6083 : totK PD2M8K2 D2M8K2.t6083 = [0, 0, 213554220365, 475042793105, 203542587565, 11066126582, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
