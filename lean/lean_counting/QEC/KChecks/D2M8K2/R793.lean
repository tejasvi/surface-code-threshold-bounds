import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3172 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3172 = true := by
  decide +kernel

theorem tot3172 : totK PD2M8K2 D2M8K2.t3172 = [0, 179209084633, 480002817073, 229258235069, 9381973547, 0, 0, 0] := by
  decide +kernel

theorem rows3173 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3173 = true := by
  decide +kernel

theorem tot3173 : totK PD2M8K2 D2M8K2.t3173 = [120687743152, 351579661897, 311381982609, 114944641185, 6775760191, 0, 0, 0] := by
  decide +kernel

theorem rows3174 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3174 = true := by
  decide +kernel

theorem tot3174 : totK PD2M8K2 D2M8K2.t3174 = [170244865317, 449004001777, 279607716564, 30360088343, 0, 0, 0, 0] := by
  decide +kernel

theorem rows3175 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3175 = true := by
  decide +kernel

theorem tot3175 : totK PD2M8K2 D2M8K2.t3175 = [155093505832, 453648321724, 279070494746, 19811840447, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
