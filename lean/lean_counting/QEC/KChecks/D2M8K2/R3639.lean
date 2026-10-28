import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14556 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14556 = true := by
  decide +kernel

theorem tot14556 : totK PD2M8K2 D2M8K2.t14556 = [0, 207165696892, 475502292431, 198916283178, 7689860642, 0, 0, 0] := by
  decide +kernel

theorem rows14557 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14557 = true := by
  decide +kernel

theorem tot14557 : totK PD2M8K2 D2M8K2.t14557 = [0, 159208124790, 462167314714, 251686998804, 16936124968, 0, 0, 0] := by
  decide +kernel

theorem rows14558 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14558 = true := by
  decide +kernel

theorem tot14558 : totK PD2M8K2 D2M8K2.t14558 = [0, 179801336674, 461295242236, 231368042558, 16691388709, 0, 0, 0] := by
  decide +kernel

theorem rows14559 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14559 = true := by
  decide +kernel

theorem tot14559 : totK PD2M8K2 D2M8K2.t14559 = [0, 0, 285809116599, 472512191121, 90367494064, 1095107716, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
