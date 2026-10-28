import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7756 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7756 = true := by
  decide +kernel

theorem tot7756 : totK PD2M8K2 D2M8K2.t7756 = [0, 0, 0, 191149223889, 456439921910, 233785986499, 18095854657, 0] := by
  decide +kernel

theorem rows7757 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7757 = true := by
  decide +kernel

theorem tot7757 : totK PD2M8K2 D2M8K2.t7757 = [0, 0, 0, 207824127958, 478414235272, 178657449451, 7651299259, 0] := by
  decide +kernel

theorem rows7758 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7758 = true := by
  decide +kernel

theorem tot7758 : totK PD2M8K2 D2M8K2.t7758 = [0, 0, 0, 264492301153, 458910768561, 124060503231, 5017339174, 0] := by
  decide +kernel

theorem rows7759 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7759 = true := by
  decide +kernel

theorem tot7759 : totK PD2M8K2 D2M8K2.t7759 = [0, 0, 0, 203809200165, 473571561698, 182149708855, 10818414931, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
