import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows640 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t640 = true := by
  decide +kernel

theorem tot640 : totK PD2M8K2 D2M8K2.t640 = [0, 53027278352, 224453290927, 417138509549, 182630049304, 7877424857, 0, 0] := by
  decide +kernel

theorem rows641 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t641 = true := by
  decide +kernel

theorem tot641 : totK PD2M8K2 D2M8K2.t641 = [0, 195710738941, 463418940989, 241655664328, 22993104267, 0, 0, 0] := by
  decide +kernel

theorem rows642 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t642 = true := by
  decide +kernel

theorem tot642 : totK PD2M8K2 D2M8K2.t642 = [0, 171714689483, 476619103235, 231671118677, 12423391470, 0, 0, 0] := by
  decide +kernel

theorem rows643 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t643 = true := by
  decide +kernel

theorem tot643 : totK PD2M8K2 D2M8K2.t643 = [0, 0, 320279533260, 498196809853, 84875532813, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
