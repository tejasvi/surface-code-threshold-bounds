import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3816 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3816 = true := by
  decide +kernel

theorem tot3816 : totK PD2M8K2 D2M8K2.t3816 = [0, 193811780839, 455760689711, 258144214694, 25969295659, 0, 0, 0] := by
  decide +kernel

theorem rows3817 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3817 = true := by
  decide +kernel

theorem tot3817 : totK PD2M8K2 D2M8K2.t3817 = [0, 204031915169, 489106829697, 209666027976, 11276447401, 0, 0, 0] := by
  decide +kernel

theorem rows3818 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3818 = true := by
  decide +kernel

theorem tot3818 : totK PD2M8K2 D2M8K2.t3818 = [0, 172882538255, 475078695939, 234855006875, 16385404038, 0, 0, 0] := by
  decide +kernel

theorem rows3819 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3819 = true := by
  decide +kernel

theorem tot3819 : totK PD2M8K2 D2M8K2.t3819 = [0, 175185964103, 442245646459, 263473761980, 23705995514, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
