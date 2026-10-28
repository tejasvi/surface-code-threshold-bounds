import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows16164 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16164 = true := by
  decide +kernel

theorem tot16164 : totK PD2M8K2 D2M8K2.t16164 = [0, 174722584143, 453440257064, 238931078106, 14658663915, 0, 0, 0] := by
  decide +kernel

theorem rows16165 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16165 = true := by
  decide +kernel

theorem tot16165 : totK PD2M8K2 D2M8K2.t16165 = [0, 73209924975, 339476355747, 391316704323, 88842638706, 1369150432, 0, 0] := by
  decide +kernel

theorem rows16166 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16166 = true := by
  decide +kernel

theorem tot16166 : totK PD2M8K2 D2M8K2.t16166 = [0, 37702770813, 343060343164, 468731630186, 58529510021, 0, 0, 0] := by
  decide +kernel

theorem rows16167 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16167 = true := by
  decide +kernel

theorem tot16167 : totK PD2M8K2 D2M8K2.t16167 = [0, 188968405241, 451332869690, 261976913661, 27755681328, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
