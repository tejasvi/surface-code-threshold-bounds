import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3484 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3484 = true := by
  decide +kernel

theorem tot3484 : totK PD2M8K2 D2M8K2.t3484 = [197428605011, 459953188626, 232046686753, 17094477172, 0, 0, 0, 0] := by
  decide +kernel

theorem rows3485 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3485 = true := by
  decide +kernel

theorem tot3485 : totK PD2M8K2 D2M8K2.t3485 = [36702169794, 332927071993, 427918691820, 83571559998, 1096505104, 0, 0, 0] := by
  decide +kernel

theorem rows3486 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3486 = true := by
  decide +kernel

theorem tot3486 : totK PD2M8K2 D2M8K2.t3486 = [31980950147, 276337799919, 466989333133, 122278806726, 3884009855, 0, 0, 0] := by
  decide +kernel

theorem rows3487 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3487 = true := by
  decide +kernel

theorem tot3487 : totK PD2M8K2 D2M8K2.t3487 = [187038956864, 468340089031, 247043751601, 23168974559, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
