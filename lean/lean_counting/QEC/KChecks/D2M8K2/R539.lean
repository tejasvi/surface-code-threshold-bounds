import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2156 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2156 = true := by
  decide +kernel

theorem tot2156 : totK PD2M8K2 D2M8K2.t2156 = [0, 0, 174860911094, 487698440911, 227733668744, 12940973730, 0, 0] := by
  decide +kernel

theorem rows2157 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2157 = true := by
  decide +kernel

theorem tot2157 : totK PD2M8K2 D2M8K2.t2157 = [0, 0, 211819020658, 467444489453, 213338093476, 11322268024, 0, 0] := by
  decide +kernel

theorem rows2158 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2158 = true := by
  decide +kernel

theorem tot2158 : totK PD2M8K2 D2M8K2.t2158 = [0, 0, 175620817414, 462532807562, 248841295949, 18658034475, 0, 0] := by
  decide +kernel

theorem rows2159 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2159 = true := by
  decide +kernel

theorem tot2159 : totK PD2M8K2 D2M8K2.t2159 = [0, 0, 174371471792, 474126488112, 226442623091, 8862649597, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
