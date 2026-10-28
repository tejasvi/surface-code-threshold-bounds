import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8156 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8156 = true := by
  decide +kernel

theorem tot8156 : totK PD2M8K2 D2M8K2.t8156 = [0, 0, 187792215116, 459910540569, 242105379066, 21425747690, 0, 0] := by
  decide +kernel

theorem rows8157 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8157 = true := by
  decide +kernel

theorem tot8157 : totK PD2M8K2 D2M8K2.t8157 = [0, 0, 219492774060, 494471740554, 187358703927, 5430665091, 0, 0] := by
  decide +kernel

theorem rows8158 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8158 = true := by
  decide +kernel

theorem tot8158 : totK PD2M8K2 D2M8K2.t8158 = [0, 172473517199, 378955387605, 237605423456, 104108973450, 6799735859, 0, 0] := by
  decide +kernel

theorem rows8159 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8159 = true := by
  decide +kernel

theorem tot8159 : totK PD2M8K2 D2M8K2.t8159 = [0, 164828638535, 443766874928, 273614174965, 20646059877, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
