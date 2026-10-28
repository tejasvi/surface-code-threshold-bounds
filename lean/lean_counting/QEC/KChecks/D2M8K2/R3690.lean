import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14760 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14760 = true := by
  decide +kernel

theorem tot14760 : totK PD2M8K2 D2M8K2.t14760 = [0, 207663220099, 472303419462, 218300426060, 11211664697, 0, 0, 0] := by
  decide +kernel

theorem rows14761 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14761 = true := by
  decide +kernel

theorem tot14761 : totK PD2M8K2 D2M8K2.t14761 = [0, 200042738501, 480441648897, 209093035052, 7870241454, 0, 0, 0] := by
  decide +kernel

theorem rows14762 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14762 = true := by
  decide +kernel

theorem tot14762 : totK PD2M8K2 D2M8K2.t14762 = [134721454216, 320606269715, 317233761571, 145605121918, 13468148062, 0, 0, 0] := by
  decide +kernel

theorem rows14763 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14763 = true := by
  decide +kernel

theorem tot14763 : totK PD2M8K2 D2M8K2.t14763 = [182561379861, 470479027638, 239112762056, 16431405026, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
