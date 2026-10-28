import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11956 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11956 = true := by
  decide +kernel

theorem tot11956 : totK PD2M8K2 D2M8K2.t11956 = [0, 126923202586, 440169499835, 284126744408, 20023055003, 0, 0, 0] := by
  decide +kernel

theorem rows11957 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11957 = true := by
  decide +kernel

theorem tot11957 : totK PD2M8K2 D2M8K2.t11957 = [0, 0, 283895905546, 482052885400, 84321534330, 1239866073, 0, 0] := by
  decide +kernel

theorem rows11958 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11958 = true := by
  decide +kernel

theorem tot11958 : totK PD2M8K2 D2M8K2.t11958 = [0, 160954566518, 440782338698, 289941729189, 32695205224, 0, 0, 0] := by
  decide +kernel

theorem rows11959 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11959 = true := by
  decide +kernel

theorem tot11959 : totK PD2M8K2 D2M8K2.t11959 = [0, 188819910985, 473185750797, 230483484621, 12498082936, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
