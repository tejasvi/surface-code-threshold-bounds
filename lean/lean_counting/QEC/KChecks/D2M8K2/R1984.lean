import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7936 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7936 = true := by
  decide +kernel

theorem tot7936 : totK PD2M8K2 D2M8K2.t7936 = [0, 0, 196201529704, 472382069960, 218253035363, 12370590376, 0, 0] := by
  decide +kernel

theorem rows7937 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7937 = true := by
  decide +kernel

theorem tot7937 : totK PD2M8K2 D2M8K2.t7937 = [0, 0, 184525022204, 476633928199, 206124706855, 10541049727, 0, 0] := by
  decide +kernel

theorem rows7938 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7938 = true := by
  decide +kernel

theorem tot7938 : totK PD2M8K2 D2M8K2.t7938 = [0, 0, 178859998735, 462162814878, 237639080082, 13908012088, 0, 0] := by
  decide +kernel

theorem rows7939 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7939 = true := by
  decide +kernel

theorem tot7939 : totK PD2M8K2 D2M8K2.t7939 = [0, 0, 207214032880, 485848402400, 184503796729, 5261966441, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
