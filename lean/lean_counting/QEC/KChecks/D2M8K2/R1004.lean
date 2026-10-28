import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4016 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4016 = true := by
  decide +kernel

theorem tot4016 : totK PD2M8K2 D2M8K2.t4016 = [0, 180409363123, 459969683451, 256174466246, 21010111118, 0, 0, 0] := by
  decide +kernel

theorem rows4017 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4017 = true := by
  decide +kernel

theorem tot4017 : totK PD2M8K2 D2M8K2.t4017 = [0, 175080372691, 474628225448, 256377681765, 20620502005, 0, 0, 0] := by
  decide +kernel

theorem rows4018 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4018 = true := by
  decide +kernel

theorem tot4018 : totK PD2M8K2 D2M8K2.t4018 = [0, 0, 172721490616, 446497332000, 259783766415, 25373788367, 0, 0] := by
  decide +kernel

theorem rows4019 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4019 = true := by
  decide +kernel

theorem tot4019 : totK PD2M8K2 D2M8K2.t4019 = [0, 0, 210162996160, 500509653370, 195278491726, 5430665091, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
