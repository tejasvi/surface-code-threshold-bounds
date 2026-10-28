import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4916 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4916 = true := by
  decide +kernel

theorem tot4916 : totK PA10K2 A10K2.t4916 = [0, 680815854771, 2162290636634, 1606911439329, 261519673769, 6354482628, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4917 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4917 = true := by
  decide +kernel

theorem tot4917 : totK PA10K2 A10K2.t4917 = [0, 494480546709, 1814971769264, 1884084528245, 541467592690, 31987876949, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4918 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4918 = true := by
  decide +kernel

theorem tot4918 : totK PA10K2 A10K2.t4918 = [0, 478912059307, 1780193326465, 1970045882221, 564494308900, 32470943963, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4919 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4919 = true := by
  decide +kernel

theorem tot4919 : totK PA10K2 A10K2.t4919 = [0, 509008125055, 1802393023020, 1893355753310, 509054466642, 31607162994, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
