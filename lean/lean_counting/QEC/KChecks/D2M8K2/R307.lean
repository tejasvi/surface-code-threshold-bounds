import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1228 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1228 = true := by
  decide +kernel

theorem tot1228 : totK PD2M8K2 D2M8K2.t1228 = [0, 173756618964, 439997797495, 271792564344, 28415688176, 0, 0, 0] := by
  decide +kernel

theorem rows1229 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1229 = true := by
  decide +kernel

theorem tot1229 : totK PD2M8K2 D2M8K2.t1229 = [0, 162095440343, 477107307309, 262333196859, 11023846051, 0, 0, 0] := by
  decide +kernel

theorem rows1230 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1230 = true := by
  decide +kernel

theorem tot1230 : totK PD2M8K2 D2M8K2.t1230 = [0, 0, 204576351888, 462640607103, 216622077055, 21385604922, 0, 0] := by
  decide +kernel

theorem rows1231 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1231 = true := by
  decide +kernel

theorem tot1231 : totK PD2M8K2 D2M8K2.t1231 = [0, 0, 190992569976, 467036217917, 213803229365, 9012177970, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
