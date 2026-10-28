import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10668 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10668 = true := by
  decide +kernel

theorem tot10668 : totK PD2M8K2 D2M8K2.t10668 = [0, 0, 149401326491, 453961797296, 260299416368, 18810355503, 0, 0] := by
  decide +kernel

theorem rows10669 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10669 = true := by
  decide +kernel

theorem tot10669 : totK PD2M8K2 D2M8K2.t10669 = [0, 0, 0, 301333708696, 498199242044, 68735007736, 1164319620, 0] := by
  decide +kernel

theorem rows10670 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10670 = true := by
  decide +kernel

theorem tot10670 : totK PD2M8K2 D2M8K2.t10670 = [0, 0, 191123103048, 462754761398, 239991697927, 14687952195, 0, 0] := by
  decide +kernel

theorem rows10671 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10671 = true := by
  decide +kernel

theorem tot10671 : totK PD2M8K2 D2M8K2.t10671 = [0, 0, 183054521645, 468096770281, 228865230504, 12523541424, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
