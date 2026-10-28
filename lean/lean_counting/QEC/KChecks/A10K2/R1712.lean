import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6848 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6848 = true := by
  decide +kernel

theorem tot6848 : totK PA10K2 A10K2.t6848 = [0, 613762948205, 2021051970016, 1911629625812, 482011358308, 25761627668, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6849 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6849 = true := by
  decide +kernel

theorem tot6849 : totK PA10K2 A10K2.t6849 = [0, 0, 790721342391, 2315377455195, 1729248932021, 278464560412, 6279851884, 0, 0, 0] := by
  decide +kernel

theorem rows6850 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6850 = true := by
  decide +kernel

theorem tot6850 : totK PA10K2 A10K2.t6850 = [0, 0, 437187003657, 1739985497612, 2111326376991, 744173456167, 56084282801, 0, 0, 0] := by
  decide +kernel

theorem rows6851 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6851 = true := by
  decide +kernel

theorem tot6851 : totK PA10K2 A10K2.t6851 = [0, 0, 465351867234, 1755550517144, 1873641546455, 528204953511, 31741948405, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
