import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9052 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9052 = true := by
  decide +kernel

theorem tot9052 : totK PD2M8K2 D2M8K2.t9052 = [0, 98520090064, 347573468440, 366690313823, 79357300704, 1227322468, 0, 0] := by
  decide +kernel

theorem rows9053 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9053 = true := by
  decide +kernel

theorem tot9053 : totK PD2M8K2 D2M8K2.t9053 = [0, 170790659051, 442060281949, 280426392597, 30585669717, 0, 0, 0] := by
  decide +kernel

theorem rows9054 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9054 = true := by
  decide +kernel

theorem tot9054 : totK PD2M8K2 D2M8K2.t9054 = [0, 157534451182, 460394172604, 264712571363, 18224375022, 0, 0, 0] := by
  decide +kernel

theorem rows9055 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9055 = true := by
  decide +kernel

theorem tot9055 : totK PD2M8K2 D2M8K2.t9055 = [0, 0, 223072382239, 495717947819, 171210889540, 7210114369, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
