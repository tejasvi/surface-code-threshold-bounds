import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15492 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15492 = true := by
  decide +kernel

theorem tot15492 : totK PD2M8K2 D2M8K2.t15492 = [0, 0, 162292036434, 444458915289, 274171568626, 27741939258, 0, 0] := by
  decide +kernel

theorem rows15493 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15493 = true := by
  decide +kernel

theorem tot15493 : totK PD2M8K2 D2M8K2.t15493 = [0, 0, 103338323929, 395537845117, 333765901740, 48256573772, 1075657031, 0] := by
  decide +kernel

theorem rows15494 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15494 = true := by
  decide +kernel

theorem tot15494 : totK PD2M8K2 D2M8K2.t15494 = [0, 0, 0, 270140692002, 479349382105, 115362546507, 3804183361, 0] := by
  decide +kernel

theorem rows15495 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15495 = true := by
  decide +kernel

theorem tot15495 : totK PD2M8K2 D2M8K2.t15495 = [0, 0, 166659160540, 453505471146, 267420461980, 30192499225, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
