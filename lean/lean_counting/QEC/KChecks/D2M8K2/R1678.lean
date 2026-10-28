import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6712 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6712 = true := by
  decide +kernel

theorem tot6712 : totK PD2M8K2 D2M8K2.t6712 = [0, 0, 315070119587, 515000265302, 86634626263, 1069412848, 0, 0] := by
  decide +kernel

theorem rows6713 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6713 = true := by
  decide +kernel

theorem tot6713 : totK PD2M8K2 D2M8K2.t6713 = [0, 0, 173285152102, 480810600213, 203262627089, 10978189672, 0, 0] := by
  decide +kernel

theorem rows6714 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6714 = true := by
  decide +kernel

theorem tot6714 : totK PD2M8K2 D2M8K2.t6714 = [0, 0, 186384783566, 462337049797, 201698754322, 13787020959, 0, 0] := by
  decide +kernel

theorem rows6715 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6715 = true := by
  decide +kernel

theorem tot6715 : totK PD2M8K2 D2M8K2.t6715 = [0, 0, 45381523314, 342186140346, 365566469656, 65801031574, 1138244013, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
