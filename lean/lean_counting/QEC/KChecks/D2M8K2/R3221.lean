import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12884 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12884 = true := by
  decide +kernel

theorem tot12884 : totK PD2M8K2 D2M8K2.t12884 = [0, 0, 93237485209, 436884175025, 359122192772, 33443544636, 0, 0] := by
  decide +kernel

theorem rows12885 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12885 = true := by
  decide +kernel

theorem tot12885 : totK PD2M8K2 D2M8K2.t12885 = [0, 0, 0, 236480496947, 495057079229, 139257723269, 2679002914, 0] := by
  decide +kernel

theorem rows12886 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12886 = true := by
  decide +kernel

theorem tot12886 : totK PD2M8K2 D2M8K2.t12886 = [0, 179984371288, 396108715062, 135392188679, 92341942857, 90857185904, 7618107313, 0] := by
  decide +kernel

theorem rows12887 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12887 = true := by
  decide +kernel

theorem tot12887 : totK PD2M8K2 D2M8K2.t12887 = [0, 167789094931, 457245914862, 236385071924, 17044607505, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
