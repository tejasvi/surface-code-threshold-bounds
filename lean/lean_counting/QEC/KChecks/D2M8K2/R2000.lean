import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8000 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8000 = true := by
  decide +kernel

theorem tot8000 : totK PD2M8K2 D2M8K2.t8000 = [0, 0, 21860994775, 274359489215, 478085927960, 114461878187, 3884009855, 0] := by
  decide +kernel

theorem rows8001 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8001 = true := by
  decide +kernel

theorem tot8001 : totK PD2M8K2 D2M8K2.t8001 = [0, 0, 198631149273, 476571598998, 223172926720, 16621220557, 0, 0] := by
  decide +kernel

theorem rows8002 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8002 = true := by
  decide +kernel

theorem tot8002 : totK PD2M8K2 D2M8K2.t8002 = [0, 0, 119442139608, 440477302283, 321099833241, 24160576526, 0, 0] := by
  decide +kernel

theorem rows8003 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8003 = true := by
  decide +kernel

theorem tot8003 : totK PD2M8K2 D2M8K2.t8003 = [0, 0, 0, 228481622207, 498012957833, 154122187513, 4880895167, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
