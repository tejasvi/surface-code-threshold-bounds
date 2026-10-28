import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows824 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t824 = true := by
  decide +kernel

theorem tot824 : totK PD2M8K2 D2M8K2.t824 = [0, 92620862180, 374308059758, 367301444112, 63622661268, 1268739303, 0, 0] := by
  decide +kernel

theorem rows825 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t825 = true := by
  decide +kernel

theorem tot825 : totK PD2M8K2 D2M8K2.t825 = [0, 0, 241375185225, 497884120327, 136357099415, 2006349614, 0, 0] := by
  decide +kernel

theorem rows826 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t826 = true := by
  decide +kernel

theorem tot826 : totK PD2M8K2 D2M8K2.t826 = [0, 0, 181714325826, 457856387294, 223626909017, 15251209721, 0, 0] := by
  decide +kernel

theorem rows827 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t827 = true := by
  decide +kernel

theorem tot827 : totK PD2M8K2 D2M8K2.t827 = [0, 0, 184547190089, 482550790188, 195739311037, 9656040098, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
