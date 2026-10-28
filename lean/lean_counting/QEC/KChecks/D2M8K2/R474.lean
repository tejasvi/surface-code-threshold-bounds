import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1896 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1896 = true := by
  decide +kernel

theorem tot1896 : totK PD2M8K2 D2M8K2.t1896 = [0, 0, 90858976459, 416214864229, 345261977847, 34070399966, 0, 0] := by
  decide +kernel

theorem rows1897 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1897 = true := by
  decide +kernel

theorem tot1897 : totK PD2M8K2 D2M8K2.t1897 = [0, 0, 196769339337, 474886419133, 218087670344, 11158772581, 0, 0] := by
  decide +kernel

theorem rows1898 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1898 = true := by
  decide +kernel

theorem tot1898 : totK PD2M8K2 D2M8K2.t1898 = [0, 0, 178152564165, 496732863385, 208151813986, 5345456729, 0, 0] := by
  decide +kernel

theorem rows1899 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1899 = true := by
  decide +kernel

theorem tot1899 : totK PD2M8K2 D2M8K2.t1899 = [0, 0, 178268690934, 457363685155, 242332679038, 18246066036, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
