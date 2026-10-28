import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10144 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10144 = true := by
  decide +kernel

theorem tot10144 : totK PD2M8K2 D2M8K2.t10144 = [0, 0, 201905130586, 472990830768, 195679926360, 12135264383, 0, 0] := by
  decide +kernel

theorem rows10145 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10145 = true := by
  decide +kernel

theorem tot10145 : totK PD2M8K2 D2M8K2.t10145 = [0, 0, 177523984124, 451902020124, 262060369832, 25831956275, 0, 0] := by
  decide +kernel

theorem rows10146 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10146 = true := by
  decide +kernel

theorem tot10146 : totK PD2M8K2 D2M8K2.t10146 = [0, 0, 192699375572, 477273499852, 211806136237, 14179944327, 0, 0] := by
  decide +kernel

theorem rows10147 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10147 = true := by
  decide +kernel

theorem tot10147 : totK PD2M8K2 D2M8K2.t10147 = [0, 0, 170857074169, 474700722611, 239209148910, 11068810259, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
