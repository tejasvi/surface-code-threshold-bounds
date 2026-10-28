import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8988 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8988 = true := by
  decide +kernel

theorem tot8988 : totK PD2M8K2 D2M8K2.t8988 = [84940856143, 325363288935, 379781413324, 112329801080, 5912535468, 0, 0, 0] := by
  decide +kernel

theorem rows8989 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8989 = true := by
  decide +kernel

theorem tot8989 : totK PD2M8K2 D2M8K2.t8989 = [180708797981, 458049589134, 256105909922, 24258469365, 0, 0, 0, 0] := by
  decide +kernel

theorem rows8990 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8990 = true := by
  decide +kernel

theorem tot8990 : totK PD2M8K2 D2M8K2.t8990 = [161514634060, 469114178285, 268795511506, 15144967138, 0, 0, 0, 0] := by
  decide +kernel

theorem rows8991 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8991 = true := by
  decide +kernel

theorem tot8991 : totK PD2M8K2 D2M8K2.t8991 = [0, 275002294593, 507744484099, 116205540016, 1198073392, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
