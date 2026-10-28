import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8064 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8064 = true := by
  decide +kernel

theorem tot8064 : totK PD2M8K2 D2M8K2.t8064 = [0, 0, 201608464688, 481721122958, 186612820770, 7442000727, 0, 0] := by
  decide +kernel

theorem rows8065 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8065 = true := by
  decide +kernel

theorem tot8065 : totK PD2M8K2 D2M8K2.t8065 = [0, 0, 186783015610, 477091630631, 217405927196, 14707859566, 0, 0] := by
  decide +kernel

theorem rows8066 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8066 = true := by
  decide +kernel

theorem tot8066 : totK PD2M8K2 D2M8K2.t8066 = [0, 0, 179860625346, 461386390109, 205142530973, 12453161582, 0, 0] := by
  decide +kernel

theorem rows8067 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8067 = true := by
  decide +kernel

theorem tot8067 : totK PD2M8K2 D2M8K2.t8067 = [0, 0, 88265605660, 380829819802, 336291569639, 60429061664, 1369150432, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
