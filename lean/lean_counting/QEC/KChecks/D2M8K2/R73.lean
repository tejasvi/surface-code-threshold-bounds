import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows292 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t292 = true := by
  decide +kernel

theorem tot292 : totK PD2M8K2 D2M8K2.t292 = [166371181139, 461394888611, 259753182676, 14293424525, 0, 0, 0, 0] := by
  decide +kernel

theorem rows293 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t293 = true := by
  decide +kernel

theorem tot293 : totK PD2M8K2 D2M8K2.t293 = [0, 204836459161, 483657637522, 182546028289, 9668735432, 0, 0, 0] := by
  decide +kernel

theorem rows294 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t294 = true := by
  decide +kernel

theorem tot294 : totK PD2M8K2 D2M8K2.t294 = [86962131354, 339656526207, 358671682518, 97703550796, 3581949829, 0, 0, 0] := by
  decide +kernel

theorem rows295 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t295 = true := by
  decide +kernel

theorem tot295 : totK PD2M8K2 D2M8K2.t295 = [176581353473, 439504860451, 249912859771, 25282354604, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
