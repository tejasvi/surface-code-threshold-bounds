import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11388 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11388 = true := by
  decide +kernel

theorem tot11388 : totK PD2M8K2 D2M8K2.t11388 = [0, 0, 218878833193, 463094346446, 161317052096, 7182288656, 0, 0] := by
  decide +kernel

theorem rows11389 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11389 = true := by
  decide +kernel

theorem tot11389 : totK PD2M8K2 D2M8K2.t11389 = [0, 94445126902, 303890972185, 360430719715, 147308490672, 13326740810, 0, 0] := by
  decide +kernel

theorem rows11390 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11390 = true := by
  decide +kernel

theorem tot11390 : totK PD2M8K2 D2M8K2.t11390 = [0, 191197009035, 460798269724, 240016513800, 19170348332, 0, 0, 0] := by
  decide +kernel

theorem rows11391 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11391 = true := by
  decide +kernel

theorem tot11391 : totK PD2M8K2 D2M8K2.t11391 = [0, 163776915475, 466742282742, 265861119163, 24839593554, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
