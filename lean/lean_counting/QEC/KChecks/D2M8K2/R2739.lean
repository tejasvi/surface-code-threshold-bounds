import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10956 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10956 = true := by
  decide +kernel

theorem tot10956 : totK PD2M8K2 D2M8K2.t10956 = [0, 292315183571, 511082607541, 97031399291, 1069412848, 0, 0, 0] := by
  decide +kernel

theorem rows10957 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10957 = true := by
  decide +kernel

theorem tot10957 : totK PD2M8K2 D2M8K2.t10957 = [192703141660, 434894478349, 221698465813, 43395968656, 2814597007, 0, 0, 0] := by
  decide +kernel

theorem rows10958 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10958 = true := by
  decide +kernel

theorem tot10958 : totK PD2M8K2 D2M8K2.t10958 = [185668564139, 452353097597, 232572960178, 17033427234, 0, 0, 0, 0] := by
  decide +kernel

theorem rows10959 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10959 = true := by
  decide +kernel

theorem tot10959 : totK PD2M8K2 D2M8K2.t10959 = [23716108948, 307707125155, 460830511712, 99559374339, 1268739303, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
