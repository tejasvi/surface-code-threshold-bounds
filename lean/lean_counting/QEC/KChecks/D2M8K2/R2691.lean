import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10764 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10764 = true := by
  decide +kernel

theorem tot10764 : totK PD2M8K2 D2M8K2.t10764 = [0, 0, 0, 193549953809, 470356402553, 203490260771, 12337737162, 0] := by
  decide +kernel

theorem rows10765 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10765 = true := by
  decide +kernel

theorem tot10765 : totK PD2M8K2 D2M8K2.t10765 = [0, 0, 0, 205649906160, 473897022590, 197024262557, 11100067333, 0] := by
  decide +kernel

theorem rows10766 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10766 = true := by
  decide +kernel

theorem tot10766 : totK PD2M8K2 D2M8K2.t10766 = [0, 0, 0, 190286219539, 476431964211, 199822160737, 11980462845, 0] := by
  decide +kernel

theorem rows10767 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10767 = true := by
  decide +kernel

theorem tot10767 : totK PD2M8K2 D2M8K2.t10767 = [0, 0, 0, 0, 334440912626, 434062603410, 69018688586, 1095107716] := by
  decide +kernel

end QECKChecks.D2M8K2
