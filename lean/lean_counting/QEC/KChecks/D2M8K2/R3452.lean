import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13808 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13808 = true := by
  decide +kernel

theorem tot13808 : totK PD2M8K2 D2M8K2.t13808 = [0, 0, 316030937498, 495866199981, 91690351795, 0, 0, 0] := by
  decide +kernel

theorem rows13809 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13809 = true := by
  decide +kernel

theorem tot13809 : totK PD2M8K2 D2M8K2.t13809 = [0, 50060237061, 281520303843, 396372009914, 120029813578, 5218872685, 0, 0] := by
  decide +kernel

theorem rows13810 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13810 = true := by
  decide +kernel

theorem tot13810 : totK PD2M8K2 D2M8K2.t13810 = [0, 174870107355, 444691238026, 267661959796, 28737110688, 0, 0, 0] := by
  decide +kernel

theorem rows13811 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13811 = true := by
  decide +kernel

theorem tot13811 : totK PD2M8K2 D2M8K2.t13811 = [0, 175119904775, 463533956559, 233780532910, 13690223021, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
