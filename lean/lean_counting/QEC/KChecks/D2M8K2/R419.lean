import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1676 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1676 = true := by
  decide +kernel

theorem tot1676 : totK PD2M8K2 D2M8K2.t1676 = [0, 0, 175224198452, 367484688947, 233381596694, 111834961337, 13326740810, 0] := by
  decide +kernel

theorem rows1677 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1677 = true := by
  decide +kernel

theorem tot1677 : totK PD2M8K2 D2M8K2.t1677 = [0, 0, 177492282450, 462379427909, 236370421441, 17115888737, 0, 0] := by
  decide +kernel

theorem rows1678 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1678 = true := by
  decide +kernel

theorem tot1678 : totK PD2M8K2 D2M8K2.t1678 = [0, 0, 87720539117, 397373645486, 362778921462, 45846000283, 0, 0] := by
  decide +kernel

theorem rows1679 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1679 = true := by
  decide +kernel

theorem tot1679 : totK PD2M8K2 D2M8K2.t1679 = [0, 0, 0, 289411897452, 504925316267, 99525390655, 1369150432, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
