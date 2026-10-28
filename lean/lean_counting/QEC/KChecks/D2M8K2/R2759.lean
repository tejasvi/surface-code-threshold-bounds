import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11036 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11036 = true := by
  decide +kernel

theorem tot11036 : totK PD2M8K2 D2M8K2.t11036 = [0, 19434652667, 305990993671, 458568457744, 89199916630, 1171084559, 0, 0] := by
  decide +kernel

theorem rows11037 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11037 = true := by
  decide +kernel

theorem tot11037 : totK PD2M8K2 D2M8K2.t11037 = [0, 0, 200453336671, 450847619497, 187230465404, 11934365838, 0, 0] := by
  decide +kernel

theorem rows11038 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11038 = true := by
  decide +kernel

theorem tot11038 : totK PD2M8K2 D2M8K2.t11038 = [0, 174393987857, 456439316466, 254406650611, 19635349523, 0, 0, 0] := by
  decide +kernel

theorem rows11039 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11039 = true := by
  decide +kernel

theorem tot11039 : totK PD2M8K2 D2M8K2.t11039 = [0, 198153995635, 472042105662, 209906686960, 12096313584, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
