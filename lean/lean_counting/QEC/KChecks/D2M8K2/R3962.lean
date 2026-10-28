import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15848 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15848 = true := by
  decide +kernel

theorem tot15848 : totK PD2M8K2 D2M8K2.t15848 = [0, 0, 179238291557, 482525956435, 237493918185, 11916247760, 0, 0] := by
  decide +kernel

theorem rows15849 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15849 = true := by
  decide +kernel

theorem tot15849 : totK PD2M8K2 D2M8K2.t15849 = [0, 0, 0, 312158200820, 487507030369, 100796580553, 1238673482, 0] := by
  decide +kernel

theorem rows15850 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15850 = true := by
  decide +kernel

theorem tot15850 : totK PD2M8K2 D2M8K2.t15850 = [0, 35696426385, 43685161608, 176464093853, 434460169712, 180830202165, 8063697217, 0] := by
  decide +kernel

theorem rows15851 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15851 = true := by
  decide +kernel

theorem tot15851 : totK PD2M8K2 D2M8K2.t15851 = [0, 208135210585, 481210577522, 189212360464, 8066584960, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
