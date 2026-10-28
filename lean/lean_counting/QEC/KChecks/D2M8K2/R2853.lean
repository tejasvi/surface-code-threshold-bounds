import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11412 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11412 = true := by
  decide +kernel

theorem tot11412 : totK PD2M8K2 D2M8K2.t11412 = [0, 0, 175680115246, 476351940894, 246211226543, 11075183149, 0, 0] := by
  decide +kernel

theorem rows11413 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11413 = true := by
  decide +kernel

theorem tot11413 : totK PD2M8K2 D2M8K2.t11413 = [0, 0, 0, 213542987589, 463619572941, 213137772052, 21385604922, 0] := by
  decide +kernel

theorem rows11414 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11414 = true := by
  decide +kernel

theorem tot11414 : totK PD2M8K2 D2M8K2.t11414 = [0, 0, 0, 177690801989, 470536484507, 216047906092, 9012177970, 0] := by
  decide +kernel

theorem rows11415 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11415 = true := by
  decide +kernel

theorem tot11415 : totK PD2M8K2 D2M8K2.t11415 = [0, 0, 150546653249, 349530992352, 275296145327, 106198558559, 6524090962, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
