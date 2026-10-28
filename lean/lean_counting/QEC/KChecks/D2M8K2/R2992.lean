import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11968 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11968 = true := by
  decide +kernel

theorem tot11968 : totK PD2M8K2 D2M8K2.t11968 = [0, 129473580020, 350866679983, 294430149844, 76404950737, 3667207281, 0, 0] := by
  decide +kernel

theorem rows11969 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11969 = true := by
  decide +kernel

theorem tot11969 : totK PD2M8K2 D2M8K2.t11969 = [0, 178124527245, 451188577462, 250062725366, 21666010060, 0, 0, 0] := by
  decide +kernel

theorem rows11970 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11970 = true := by
  decide +kernel

theorem tot11970 : totK PD2M8K2 D2M8K2.t11970 = [89951885854, 248603530724, 336899864298, 211794526712, 20798538164, 0, 0, 0] := by
  decide +kernel

theorem rows11971 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11971 = true := by
  decide +kernel

theorem tot11971 : totK PD2M8K2 D2M8K2.t11971 = [164146147000, 462849740080, 243643415120, 15936446759, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
