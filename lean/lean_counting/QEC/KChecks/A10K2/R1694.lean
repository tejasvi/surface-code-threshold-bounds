import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6776 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6776 = true := by
  decide +kernel

theorem tot6776 : totK PA10K2 A10K2.t6776 = [0, 401517035902, 1696598201166, 2159061177364, 816237016142, 56934571071, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6777 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6777 = true := by
  decide +kernel

theorem tot6777 : totK PA10K2 A10K2.t6777 = [0, 185056245259, 992555572045, 2048102900142, 1481517163339, 267684129569, 7007974415, 0, 0, 0] := by
  decide +kernel

theorem rows6778 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6778 = true := by
  decide +kernel

theorem tot6778 : totK PA10K2 A10K2.t6778 = [0, 478859877956, 1871209856455, 1950474871856, 540539955970, 31908368213, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6779 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6779 = true := by
  decide +kernel

theorem tot6779 : totK PA10K2 A10K2.t6779 = [0, 118398086739, 930327950486, 2072111104565, 1498446584975, 324151277422, 20328650499, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
