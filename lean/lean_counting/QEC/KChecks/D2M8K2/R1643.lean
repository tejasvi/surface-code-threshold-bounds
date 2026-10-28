import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6572 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6572 = true := by
  decide +kernel

theorem tot6572 : totK PD2M8K2 D2M8K2.t6572 = [0, 159276017617, 459607018852, 265085536868, 19338915702, 0, 0, 0] := by
  decide +kernel

theorem rows6573 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6573 = true := by
  decide +kernel

theorem tot6573 : totK PD2M8K2 D2M8K2.t6573 = [0, 91335625381, 363339568738, 348761919368, 57717782897, 1053411165, 0, 0] := by
  decide +kernel

theorem rows6574 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6574 = true := by
  decide +kernel

theorem tot6574 : totK PD2M8K2 D2M8K2.t6574 = [0, 0, 303615460071, 476519282368, 81756535353, 1021381562, 0, 0] := by
  decide +kernel

theorem rows6575 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6575 = true := by
  decide +kernel

theorem tot6575 : totK PD2M8K2 D2M8K2.t6575 = [190180602404, 455678971639, 200283215238, 20649861287, 19042000121, 2645825719, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
