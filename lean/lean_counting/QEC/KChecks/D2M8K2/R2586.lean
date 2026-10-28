import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10344 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10344 = true := by
  decide +kernel

theorem tot10344 : totK PD2M8K2 D2M8K2.t10344 = [0, 165263169996, 422961283860, 266663155378, 54595055139, 3089224145, 0, 0] := by
  decide +kernel

theorem rows10345 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10345 = true := by
  decide +kernel

theorem tot10345 : totK PD2M8K2 D2M8K2.t10345 = [0, 164319769885, 441096195467, 283197713158, 30315036932, 0, 0, 0] := by
  decide +kernel

theorem rows10346 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10346 = true := by
  decide +kernel

theorem tot10346 : totK PD2M8K2 D2M8K2.t10346 = [0, 89753051296, 405044439730, 355049075966, 49435123919, 1198073392, 0, 0] := by
  decide +kernel

theorem rows10347 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10347 = true := by
  decide +kernel

theorem tot10347 : totK PD2M8K2 D2M8K2.t10347 = [0, 0, 221432532698, 492192314459, 172626746882, 8466643012, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
