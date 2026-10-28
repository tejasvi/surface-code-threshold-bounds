import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows96 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t96 = true := by
  decide +kernel

theorem tot96 : totK PD2M8K2 D2M8K2.t96 = [0, 0, 289607535648, 485892023690, 101927602721, 1171084559, 0, 0] := by
  decide +kernel

theorem rows97 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t97 = true := by
  decide +kernel

theorem tot97 : totK PD2M8K2 D2M8K2.t97 = [0, 18351256589, 205698814335, 438546387324, 181830041447, 11934365838, 0, 0] := by
  decide +kernel

theorem rows98 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t98 = true := by
  decide +kernel

theorem tot98 : totK PD2M8K2 D2M8K2.t98 = [0, 195671094404, 470355905859, 208967020493, 11071105621, 0, 0, 0] := by
  decide +kernel

theorem rows99 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t99 = true := by
  decide +kernel

theorem tot99 : totK PD2M8K2 D2M8K2.t99 = [0, 189560868075, 473774278780, 217091707725, 12096313584, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
