import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4516 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4516 = true := by
  decide +kernel

theorem tot4516 : totK PA10K2 A10K2.t4516 = [0, 0, 573490703264, 1903437378334, 1821427527062, 426079791640, 26711552226, 0, 0, 0] := by
  decide +kernel

theorem rows4517 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4517 = true := by
  decide +kernel

theorem tot4517 : totK PA10K2 A10K2.t4517 = [0, 0, 488233504206, 1858514916426, 1977620799298, 473988591177, 17153369636, 0, 0, 0] := by
  decide +kernel

theorem rows4518 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4518 = true := by
  decide +kernel

theorem tot4518 : totK PA10K2 A10K2.t4518 = [0, 0, 489835243031, 1803755783498, 1891964993295, 478587770566, 31923085886, 0, 0, 0] := by
  decide +kernel

theorem rows4519 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4519 = true := by
  decide +kernel

theorem tot4519 : totK PA10K2 A10K2.t4519 = [0, 0, 295319067808, 1535406211190, 2039293967243, 651649160541, 43803516534, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
