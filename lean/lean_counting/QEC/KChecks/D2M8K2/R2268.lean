import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9072 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9072 = true := by
  decide +kernel

theorem tot9072 : totK PD2M8K2 D2M8K2.t9072 = [0, 0, 173494129872, 475279000519, 226165115688, 6618102278, 0, 0] := by
  decide +kernel

theorem rows9073 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9073 = true := by
  decide +kernel

theorem tot9073 : totK PD2M8K2 D2M8K2.t9073 = [0, 176308135696, 452139377413, 247206915974, 40642899740, 3960417438, 0, 0] := by
  decide +kernel

theorem rows9074 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9074 = true := by
  decide +kernel

theorem tot9074 : totK PD2M8K2 D2M8K2.t9074 = [0, 194390219930, 468674871945, 230919195822, 15810312305, 0, 0, 0] := by
  decide +kernel

theorem rows9075 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9075 = true := by
  decide +kernel

theorem tot9075 : totK PD2M8K2 D2M8K2.t9075 = [0, 71442957365, 341761179780, 398996381180, 88566321046, 1198073392, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
