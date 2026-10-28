import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12488 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12488 = true := by
  decide +kernel

theorem tot12488 : totK PD2M8K2 D2M8K2.t12488 = [0, 0, 191335934068, 467077384852, 205995565430, 12206147664, 0, 0] := by
  decide +kernel

theorem rows12489 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12489 = true := by
  decide +kernel

theorem tot12489 : totK PD2M8K2 D2M8K2.t12489 = [0, 0, 37351754996, 313683675951, 417318122983, 96722068960, 1369150432, 0] := by
  decide +kernel

theorem rows12490 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12490 = true := by
  decide +kernel

theorem tot12490 : totK PD2M8K2 D2M8K2.t12490 = [0, 0, 87493257244, 378588316385, 360091156238, 45946403621, 0, 0] := by
  decide +kernel

theorem rows12491 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12491 = true := by
  decide +kernel

theorem tot12491 : totK PD2M8K2 D2M8K2.t12491 = [0, 0, 158326225224, 479257639846, 235514036150, 11476444046, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
