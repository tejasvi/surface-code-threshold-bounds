import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4436 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4436 = true := by
  decide +kernel

theorem tot4436 : totK PD2M8K2 D2M8K2.t4436 = [0, 159278022010, 449559812512, 293357747576, 30468211203, 0, 0, 0] := by
  decide +kernel

theorem rows4437 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4437 = true := by
  decide +kernel

theorem tot4437 : totK PD2M8K2 D2M8K2.t4437 = [0, 174333546275, 469687527331, 242133984218, 13731198790, 0, 0, 0] := by
  decide +kernel

theorem rows4438 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4438 = true := by
  decide +kernel

theorem tot4438 : totK PD2M8K2 D2M8K2.t4438 = [0, 0, 201606382626, 469247609731, 225495068074, 21380920664, 0, 0] := by
  decide +kernel

theorem rows4439 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4439 = true := by
  decide +kernel

theorem tot4439 : totK PD2M8K2 D2M8K2.t4439 = [0, 0, 188898686941, 475977042439, 224320849239, 9382475930, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
