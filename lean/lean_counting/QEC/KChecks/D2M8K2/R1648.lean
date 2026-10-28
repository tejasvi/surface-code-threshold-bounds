import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6592 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6592 = true := by
  decide +kernel

theorem tot6592 : totK PD2M8K2 D2M8K2.t6592 = [177502607452, 456689136645, 268784677717, 27803404619, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6593 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6593 = true := by
  decide +kernel

theorem tot6593 : totK PD2M8K2 D2M8K2.t6593 = [180297576134, 473115331154, 240523453648, 13262355368, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6594 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6594 = true := by
  decide +kernel

theorem tot6594 : totK PD2M8K2 D2M8K2.t6594 = [0, 293093647531, 516470434449, 98477419125, 1096505104, 0, 0, 0] := by
  decide +kernel

theorem rows6595 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6595 = true := by
  decide +kernel

theorem tot6595 : totK PD2M8K2 D2M8K2.t6595 = [0, 235749406128, 500350664040, 160089611573, 5253830308, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
