import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1376 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1376 = true := by
  decide +kernel

theorem tot1376 : totK PD2M8K2 D2M8K2.t1376 = [0, 0, 211969587220, 488147515648, 187987322611, 5428656490, 0, 0] := by
  decide +kernel

theorem rows1377 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1377 = true := by
  decide +kernel

theorem tot1377 : totK PD2M8K2 D2M8K2.t1377 = [0, 0, 200096608177, 481077465884, 189568983794, 9840474482, 0, 0] := by
  decide +kernel

theorem rows1378 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1378 = true := by
  decide +kernel

theorem tot1378 : totK PD2M8K2 D2M8K2.t1378 = [0, 0, 170067798467, 490473904826, 224449234261, 6833736283, 0, 0] := by
  decide +kernel

theorem rows1379 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1379 = true := by
  decide +kernel

theorem tot1379 : totK PD2M8K2 D2M8K2.t1379 = [0, 0, 205650839107, 474727471585, 186602671568, 9841222104, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
