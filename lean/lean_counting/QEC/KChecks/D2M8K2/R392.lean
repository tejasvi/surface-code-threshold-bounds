import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1568 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1568 = true := by
  decide +kernel

theorem tot1568 : totK PD2M8K2 D2M8K2.t1568 = [0, 0, 0, 320219567131, 444430496432, 69786842810, 1021600638, 0] := by
  decide +kernel

theorem rows1569 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1569 = true := by
  decide +kernel

theorem tot1569 : totK PD2M8K2 D2M8K2.t1569 = [0, 0, 138250420949, 365756709525, 278326727511, 66295720793, 3552795014, 0] := by
  decide +kernel

theorem rows1570 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1570 = true := by
  decide +kernel

theorem tot1570 : totK PD2M8K2 D2M8K2.t1570 = [0, 0, 178998098254, 477830096659, 231576588589, 11700507236, 0, 0] := by
  decide +kernel

theorem rows1571 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1571 = true := by
  decide +kernel

theorem tot1571 : totK PD2M8K2 D2M8K2.t1571 = [0, 90907693037, 278683309430, 338976888306, 179484212410, 16332735050, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
