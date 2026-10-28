import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7412 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7412 = true := by
  decide +kernel

theorem tot7412 : totK PD2M8K2 D2M8K2.t7412 = [0, 162055487967, 453551631484, 274291455555, 26328569101, 0, 0, 0] := by
  decide +kernel

theorem rows7413 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7413 = true := by
  decide +kernel

theorem tot7413 : totK PD2M8K2 D2M8K2.t7413 = [0, 0, 177146942014, 443517026925, 251800378867, 25370006417, 0, 0] := by
  decide +kernel

theorem rows7414 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7414 = true := by
  decide +kernel

theorem tot7414 : totK PD2M8K2 D2M8K2.t7414 = [0, 0, 211452687599, 490856205255, 196287281242, 5430665091, 0, 0] := by
  decide +kernel

theorem rows7415 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7415 = true := by
  decide +kernel

theorem tot7415 : totK PD2M8K2 D2M8K2.t7415 = [0, 166416896941, 376661622645, 246877706952, 106468030169, 6801036714, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
