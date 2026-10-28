import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11064 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11064 = true := by
  decide +kernel

theorem tot11064 : totK PD2M8K2 D2M8K2.t11064 = [0, 171193335882, 455698020142, 227136206125, 16891742343, 0, 0, 0] := by
  decide +kernel

theorem rows11065 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11065 = true := by
  decide +kernel

theorem tot11065 : totK PD2M8K2 D2M8K2.t11065 = [0, 157891049441, 461069025394, 244449894580, 15898197137, 0, 0, 0] := by
  decide +kernel

theorem rows11066 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11066 = true := by
  decide +kernel

theorem tot11066 : totK PD2M8K2 D2M8K2.t11066 = [0, 0, 307928023505, 464455068807, 76948090371, 1138244013, 0, 0] := by
  decide +kernel

theorem rows11067 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11067 = true := by
  decide +kernel

theorem tot11067 : totK PD2M8K2 D2M8K2.t11067 = [0, 173438096905, 461976908033, 262179239467, 26621088621, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
