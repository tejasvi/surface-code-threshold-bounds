import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3988 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3988 = true := by
  decide +kernel

theorem tot3988 : totK PD2M8K2 D2M8K2.t3988 = [0, 0, 214964859828, 482705361970, 171131599473, 7611474319, 0, 0] := by
  decide +kernel

theorem rows3989 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3989 = true := by
  decide +kernel

theorem tot3989 : totK PD2M8K2 D2M8K2.t3989 = [0, 113620377193, 363843711983, 337583769430, 65208505364, 946121569, 0, 0] := by
  decide +kernel

theorem rows3990 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3990 = true := by
  decide +kernel

theorem tot3990 : totK PD2M8K2 D2M8K2.t3990 = [0, 160813422336, 439704654660, 276841681754, 29969113215, 0, 0, 0] := by
  decide +kernel

theorem rows3991 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3991 = true := by
  decide +kernel

theorem tot3991 : totK PD2M8K2 D2M8K2.t3991 = [0, 140770888770, 445521060346, 290216328637, 22863494529, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
