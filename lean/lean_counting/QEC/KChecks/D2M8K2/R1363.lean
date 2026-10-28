import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5452 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5452 = true := by
  decide +kernel

theorem tot5452 : totK PD2M8K2 D2M8K2.t5452 = [0, 0, 0, 204920494209, 486175013907, 186202325967, 8379551475, 0] := by
  decide +kernel

theorem rows5453 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5453 = true := by
  decide +kernel

theorem tot5453 : totK PD2M8K2 D2M8K2.t5453 = [0, 0, 239202547983, 476685150626, 200795202382, 18594096039, 0, 0] := by
  decide +kernel

theorem rows5454 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5454 = true := by
  decide +kernel

theorem tot5454 : totK PD2M8K2 D2M8K2.t5454 = [0, 0, 85965082063, 429466408343, 356179030836, 32355272371, 0, 0] := by
  decide +kernel

theorem rows5455 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5455 = true := by
  decide +kernel

theorem tot5455 : totK PD2M8K2 D2M8K2.t5455 = [0, 0, 81153721523, 328068187365, 398524376065, 84423020718, 1430229726, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
