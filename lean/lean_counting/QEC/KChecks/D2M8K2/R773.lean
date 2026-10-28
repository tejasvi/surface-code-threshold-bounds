import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3092 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3092 = true := by
  decide +kernel

theorem tot3092 : totK PD2M8K2 D2M8K2.t3092 = [0, 160294956958, 464134033345, 271872217837, 23420869805, 0, 0, 0] := by
  decide +kernel

theorem rows3093 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3093 = true := by
  decide +kernel

theorem tot3093 : totK PD2M8K2 D2M8K2.t3093 = [0, 0, 225602707945, 500099699265, 156448851249, 5228939780, 0, 0] := by
  decide +kernel

theorem rows3094 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3094 = true := by
  decide +kernel

theorem tot3094 : totK PD2M8K2 D2M8K2.t3094 = [0, 174136425926, 458259052346, 255237610350, 26532429755, 0, 0, 0] := by
  decide +kernel

theorem rows3095 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3095 = true := by
  decide +kernel

theorem tot3095 : totK PD2M8K2 D2M8K2.t3095 = [0, 172007623904, 440641859153, 273178347706, 28232646136, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
