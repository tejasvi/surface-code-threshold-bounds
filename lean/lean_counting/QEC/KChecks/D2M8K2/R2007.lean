import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8028 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8028 = true := by
  decide +kernel

theorem tot8028 : totK PD2M8K2 D2M8K2.t8028 = [0, 0, 139018417576, 438100748356, 292749220977, 19739774446, 0, 0] := by
  decide +kernel

theorem rows8029 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8029 = true := by
  decide +kernel

theorem tot8029 : totK PD2M8K2 D2M8K2.t8029 = [0, 0, 0, 288966882511, 491586518678, 92380740391, 1162740214, 0] := by
  decide +kernel

theorem rows8030 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8030 = true := by
  decide +kernel

theorem tot8030 : totK PD2M8K2 D2M8K2.t8030 = [0, 0, 174639719554, 428850826369, 223991075655, 56819494903, 3581949829, 0] := by
  decide +kernel

theorem rows8031 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8031 = true := by
  decide +kernel

theorem tot8031 : totK PD2M8K2 D2M8K2.t8031 = [0, 0, 173867905455, 441108896887, 263444889109, 26608001630, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
