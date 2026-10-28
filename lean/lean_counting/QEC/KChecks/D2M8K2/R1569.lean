import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6276 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6276 = true := by
  decide +kernel

theorem tot6276 : totK PD2M8K2 D2M8K2.t6276 = [0, 207625430326, 491795725162, 184166698925, 9583672031, 0, 0, 0] := by
  decide +kernel

theorem rows6277 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6277 = true := by
  decide +kernel

theorem tot6277 : totK PD2M8K2 D2M8K2.t6277 = [79947513563, 327850988603, 377572963274, 95060499079, 3460111309, 0, 0, 0] := by
  decide +kernel

theorem rows6278 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6278 = true := by
  decide +kernel

theorem tot6278 : totK PD2M8K2 D2M8K2.t6278 = [175123449855, 453743599297, 267583936560, 27648119458, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6279 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6279 = true := by
  decide +kernel

theorem tot6279 : totK PD2M8K2 D2M8K2.t6279 = [71619231982, 334571432538, 403332946919, 87314465994, 1198073392, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
