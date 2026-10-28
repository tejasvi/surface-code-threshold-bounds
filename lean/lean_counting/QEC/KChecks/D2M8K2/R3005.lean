import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12020 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12020 = true := by
  decide +kernel

theorem tot12020 : totK PD2M8K2 D2M8K2.t12020 = [0, 180719889946, 469942446054, 228706586153, 12816790975, 0, 0, 0] := by
  decide +kernel

theorem rows12021 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12021 = true := by
  decide +kernel

theorem tot12021 : totK PD2M8K2 D2M8K2.t12021 = [0, 215884963843, 480474215721, 181388797451, 9600062166, 0, 0, 0] := by
  decide +kernel

theorem rows12022 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12022 = true := by
  decide +kernel

theorem tot12022 : totK PD2M8K2 D2M8K2.t12022 = [0, 179208208531, 480836660909, 213551099449, 6360151198, 0, 0, 0] := by
  decide +kernel

theorem rows12023 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12023 = true := by
  decide +kernel

theorem tot12023 : totK PD2M8K2 D2M8K2.t12023 = [0, 0, 274517388481, 496657327660, 92666434599, 1310285577, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
