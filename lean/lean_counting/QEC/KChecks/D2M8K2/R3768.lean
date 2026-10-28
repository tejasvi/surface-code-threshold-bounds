import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15072 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15072 = true := by
  decide +kernel

theorem tot15072 : totK PD2M8K2 D2M8K2.t15072 = [0, 105920131535, 425292399602, 337512303387, 29127833298, 0, 0, 0] := by
  decide +kernel

theorem rows15073 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15073 = true := by
  decide +kernel

theorem tot15073 : totK PD2M8K2 D2M8K2.t15073 = [0, 0, 204259229543, 481807641255, 180667209883, 9587713104, 0, 0] := by
  decide +kernel

theorem rows15074 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15074 = true := by
  decide +kernel

theorem tot15074 : totK PD2M8K2 D2M8K2.t15074 = [0, 87978670910, 340849571690, 359491666329, 89331388820, 3462014130, 0, 0] := by
  decide +kernel

theorem rows15075 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15075 = true := by
  decide +kernel

theorem tot15075 : totK PD2M8K2 D2M8K2.t15075 = [0, 184964446223, 442370421681, 249767044596, 25700183290, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
