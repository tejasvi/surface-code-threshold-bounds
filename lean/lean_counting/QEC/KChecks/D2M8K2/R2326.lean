import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9304 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9304 = true := by
  decide +kernel

theorem tot9304 : totK PD2M8K2 D2M8K2.t9304 = [0, 195164186086, 474478374642, 199091477304, 12052611869, 0, 0, 0] := by
  decide +kernel

theorem rows9305 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9305 = true := by
  decide +kernel

theorem tot9305 : totK PD2M8K2 D2M8K2.t9305 = [175967501358, 456055632394, 267173491790, 28278807280, 0, 0, 0, 0] := by
  decide +kernel

theorem rows9306 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9306 = true := by
  decide +kernel

theorem tot9306 : totK PD2M8K2 D2M8K2.t9306 = [175428232894, 451670494985, 253363335137, 21267447540, 0, 0, 0, 0] := by
  decide +kernel

theorem rows9307 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9307 = true := by
  decide +kernel

theorem tot9307 : totK PD2M8K2 D2M8K2.t9307 = [92932490688, 361428856225, 371499201874, 74008638916, 1096505104, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
