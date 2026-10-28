import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15480 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15480 = true := by
  decide +kernel

theorem tot15480 : totK PD2M8K2 D2M8K2.t15480 = [0, 0, 221782541458, 483528004752, 181791175626, 9442547549, 0, 0] := by
  decide +kernel

theorem rows15481 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15481 = true := by
  decide +kernel

theorem tot15481 : totK PD2M8K2 D2M8K2.t15481 = [0, 114253190048, 360738315308, 340392938913, 84728725950, 2339479808, 0, 0] := by
  decide +kernel

theorem rows15482 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15482 = true := by
  decide +kernel

theorem tot15482 : totK PD2M8K2 D2M8K2.t15482 = [0, 168541316108, 449217060821, 272777061668, 29952589139, 0, 0, 0] := by
  decide +kernel

theorem rows15483 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15483 = true := by
  decide +kernel

theorem tot15483 : totK PD2M8K2 D2M8K2.t15483 = [0, 157216008323, 453724049158, 286521224177, 23341564949, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
