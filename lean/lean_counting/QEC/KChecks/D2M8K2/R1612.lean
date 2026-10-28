import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6448 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6448 = true := by
  decide +kernel

theorem tot6448 : totK PD2M8K2 D2M8K2.t6448 = [150414475504, 448235073010, 268236109867, 17473597352, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6449 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6449 = true := by
  decide +kernel

theorem tot6449 : totK PD2M8K2 D2M8K2.t6449 = [0, 245674628680, 495587195951, 138070567649, 2348440009, 0, 0, 0] := by
  decide +kernel

theorem rows6450 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6450 = true := by
  decide +kernel

theorem tot6450 : totK PD2M8K2 D2M8K2.t6450 = [72839322363, 260919343358, 378168107708, 152526650607, 10902245252, 0, 0, 0] := by
  decide +kernel

theorem rows6451 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6451 = true := by
  decide +kernel

theorem tot6451 : totK PD2M8K2 D2M8K2.t6451 = [169031514219, 457834193651, 254450739856, 20033361445, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
