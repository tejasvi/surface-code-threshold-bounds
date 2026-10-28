import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1872 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1872 = true := by
  decide +kernel

theorem tot1872 : totK PD2M8K2 D2M8K2.t1872 = [0, 0, 179354384027, 462362941195, 246935537201, 19290567205, 0, 0] := by
  decide +kernel

theorem rows1873 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1873 = true := by
  decide +kernel

theorem tot1873 : totK PD2M8K2 D2M8K2.t1873 = [0, 68882649377, 222816798886, 388688541533, 209337488356, 12864051566, 0, 0] := by
  decide +kernel

theorem rows1874 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1874 = true := by
  decide +kernel

theorem tot1874 : totK PD2M8K2 D2M8K2.t1874 = [0, 185354982582, 479509018666, 211757806309, 9852138406, 0, 0, 0] := by
  decide +kernel

theorem rows1875 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1875 = true := by
  decide +kernel

theorem tot1875 : totK PD2M8K2 D2M8K2.t1875 = [0, 155365622640, 447141247995, 265136527114, 17517682525, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
