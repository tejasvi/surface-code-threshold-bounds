import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11816 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11816 = true := by
  decide +kernel

theorem tot11816 : totK PD2M8K2 D2M8K2.t11816 = [0, 165158882730, 449147376143, 250343530688, 18130804188, 0, 0, 0] := by
  decide +kernel

theorem rows11817 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11817 = true := by
  decide +kernel

theorem tot11817 : totK PD2M8K2 D2M8K2.t11817 = [0, 65231891679, 335496663584, 386588471905, 80075886442, 1310166938, 0, 0] := by
  decide +kernel

theorem rows11818 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11818 = true := by
  decide +kernel

theorem tot11818 : totK PD2M8K2 D2M8K2.t11818 = [0, 40940246425, 345164886326, 460204063013, 52831937765, 0, 0, 0] := by
  decide +kernel

theorem rows11819 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11819 = true := by
  decide +kernel

theorem tot11819 : totK PD2M8K2 D2M8K2.t11819 = [0, 169116595512, 440099366291, 277450624368, 30465585733, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
