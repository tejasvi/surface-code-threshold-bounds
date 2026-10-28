import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6292 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6292 = true := by
  decide +kernel

theorem tot6292 : totK PD2M8K2 D2M8K2.t6292 = [0, 163061668250, 455953482522, 259550936211, 17412509285, 0, 0, 0] := by
  decide +kernel

theorem rows6293 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6293 = true := by
  decide +kernel

theorem tot6293 : totK PD2M8K2 D2M8K2.t6293 = [0, 89391013120, 341110809020, 382236180348, 70423492447, 1075657031, 0, 0] := by
  decide +kernel

theorem rows6294 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6294 = true := by
  decide +kernel

theorem tot6294 : totK PD2M8K2 D2M8K2.t6294 = [0, 0, 297115164920, 473701514178, 105055673427, 3804183361, 0, 0] := by
  decide +kernel

theorem rows6295 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6295 = true := by
  decide +kernel

theorem tot6295 : totK PD2M8K2 D2M8K2.t6295 = [0, 180814173998, 435111175844, 253907332096, 28003105011, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
