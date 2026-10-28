import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15936 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15936 = true := by
  decide +kernel

theorem tot15936 : totK PD2M8K2 D2M8K2.t15936 = [0, 0, 219178424699, 482223872096, 175060463871, 5098257138, 0, 0] := by
  decide +kernel

theorem rows15937 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15937 = true := by
  decide +kernel

theorem tot15937 : totK PD2M8K2 D2M8K2.t15937 = [0, 0, 19497166104, 304937077757, 462992044871, 87333627645, 1310285577, 0] := by
  decide +kernel

theorem rows15938 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15938 = true := by
  decide +kernel

theorem tot15938 : totK PD2M8K2 D2M8K2.t15938 = [0, 0, 92889055109, 383958841678, 392506022712, 38735185292, 0, 0] := by
  decide +kernel

theorem rows15939 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15939 = true := by
  decide +kernel

theorem tot15939 : totK PD2M8K2 D2M8K2.t15939 = [0, 0, 168005816890, 450918445602, 275887577801, 20967935863, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
