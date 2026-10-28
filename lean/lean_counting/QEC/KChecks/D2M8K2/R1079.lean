import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4316 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4316 = true := by
  decide +kernel

theorem tot4316 : totK PD2M8K2 D2M8K2.t4316 = [0, 0, 0, 240041747971, 489604365874, 160849988953, 6864846834, 0] := by
  decide +kernel

theorem rows4317 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4317 = true := by
  decide +kernel

theorem tot4317 : totK PD2M8K2 D2M8K2.t4317 = [0, 0, 118521934009, 352844661933, 318779312643, 88640798160, 2351235033, 0] := by
  decide +kernel

theorem rows4318 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4318 = true := by
  decide +kernel

theorem tot4318 : totK PD2M8K2 D2M8K2.t4318 = [0, 0, 172159093064, 443694076677, 272771717589, 30309431601, 0, 0] := by
  decide +kernel

theorem rows4319 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4319 = true := by
  decide +kernel

theorem tot4319 : totK PD2M8K2 D2M8K2.t4319 = [0, 0, 144421158936, 461442533534, 275159035772, 18574531293, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
