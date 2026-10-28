import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10564 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10564 = true := by
  decide +kernel

theorem tot10564 : totK PD2M8K2 D2M8K2.t10564 = [0, 0, 191743559662, 453405933322, 260655442624, 29603542518, 1415142070, 0] := by
  decide +kernel

theorem rows10565 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10565 = true := by
  decide +kernel

theorem tot10565 : totK PD2M8K2 D2M8K2.t10565 = [0, 43028644854, 200528065947, 407002665447, 245847982160, 18759392536, 0, 0] := by
  decide +kernel

theorem rows10566 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10566 = true := by
  decide +kernel

theorem tot10566 : totK PD2M8K2 D2M8K2.t10566 = [0, 195636726507, 479676346941, 203040668343, 9852138406, 0, 0, 0] := by
  decide +kernel

theorem rows10567 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10567 = true := by
  decide +kernel

theorem tot10567 : totK PD2M8K2 D2M8K2.t10567 = [0, 152836506888, 452353790507, 253617088372, 16430804393, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
