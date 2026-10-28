import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8384 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8384 = true := by
  decide +kernel

theorem tot8384 : totK PD2M8K2 D2M8K2.t8384 = [0, 0, 217054889243, 470668143645, 165797136810, 7182288656, 0, 0] := by
  decide +kernel

theorem rows8385 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8385 = true := by
  decide +kernel

theorem tot8385 : totK PD2M8K2 D2M8K2.t8385 = [0, 135280300897, 343674204741, 278619388314, 127133900257, 13326740810, 0, 0] := by
  decide +kernel

theorem rows8386 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8386 = true := by
  decide +kernel

theorem tot8386 : totK PD2M8K2 D2M8K2.t8386 = [0, 181005625384, 462614492961, 235549894451, 17115888737, 0, 0, 0] := by
  decide +kernel

theorem rows8387 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8387 = true := by
  decide +kernel

theorem tot8387 : totK PD2M8K2 D2M8K2.t8387 = [0, 125127392680, 440721894863, 309869716336, 28504154241, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
