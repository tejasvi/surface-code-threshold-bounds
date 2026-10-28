import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7348 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7348 = true := by
  decide +kernel

theorem tot7348 : totK PD2M8K2 D2M8K2.t7348 = [0, 170569596556, 446479701906, 285002283511, 30488455136, 0, 0, 0] := by
  decide +kernel

theorem rows7349 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7349 = true := by
  decide +kernel

theorem tot7349 : totK PD2M8K2 D2M8K2.t7349 = [0, 196620195644, 487406045224, 208831912329, 10330900726, 0, 0, 0] := by
  decide +kernel

theorem rows7350 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7350 = true := by
  decide +kernel

theorem tot7350 : totK PD2M8K2 D2M8K2.t7350 = [0, 0, 243888870485, 454480628383, 196795890956, 21395095148, 0, 0] := by
  decide +kernel

theorem rows7351 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7351 = true := by
  decide +kernel

theorem tot7351 : totK PD2M8K2 D2M8K2.t7351 = [0, 0, 174006325073, 487031362787, 222504763188, 7992090037, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
