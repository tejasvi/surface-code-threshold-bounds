import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14484 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14484 = true := by
  decide +kernel

theorem tot14484 : totK PD2M8K2 D2M8K2.t14484 = [0, 141692357843, 388831166662, 308894898775, 63520694212, 1149959346, 0, 0] := by
  decide +kernel

theorem rows14485 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14485 = true := by
  decide +kernel

theorem tot14485 : totK PD2M8K2 D2M8K2.t14485 = [0, 164655306204, 432727863033, 285086786381, 30435264497, 0, 0, 0] := by
  decide +kernel

theorem rows14486 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14486 = true := by
  decide +kernel

theorem tot14486 : totK PD2M8K2 D2M8K2.t14486 = [0, 113110112629, 447660081987, 306290672523, 25006165733, 0, 0, 0] := by
  decide +kernel

theorem rows14487 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14487 = true := by
  decide +kernel

theorem tot14487 : totK PD2M8K2 D2M8K2.t14487 = [0, 0, 240704236309, 500209727690, 138397408810, 4031931762, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
