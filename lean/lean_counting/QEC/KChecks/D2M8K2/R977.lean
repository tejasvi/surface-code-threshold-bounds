import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3908 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3908 = true := by
  decide +kernel

theorem tot3908 : totK PD2M8K2 D2M8K2.t3908 = [0, 71082290445, 329070989835, 401845074355, 93282485549, 1429815836, 0, 0] := by
  decide +kernel

theorem rows3909 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3909 = true := by
  decide +kernel

theorem tot3909 : totK PD2M8K2 D2M8K2.t3909 = [0, 177816170080, 454920312408, 268280218117, 27868707442, 0, 0, 0] := by
  decide +kernel

theorem rows3910 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3910 = true := by
  decide +kernel

theorem tot3910 : totK PD2M8K2 D2M8K2.t3910 = [0, 180127341725, 461661210313, 251517098155, 14895440396, 0, 0, 0] := by
  decide +kernel

theorem rows3911 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3911 = true := by
  decide +kernel

theorem tot3911 : totK PD2M8K2 D2M8K2.t3911 = [0, 0, 266946080864, 505520109795, 126440925192, 1248762627, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
