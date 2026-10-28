import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows880 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t880 = true := by
  decide +kernel

theorem tot880 : totK PD2M8K2 D2M8K2.t880 = [0, 0, 204052147651, 503238171884, 196276402829, 5290448418, 0, 0] := by
  decide +kernel

theorem rows881 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t881 = true := by
  decide +kernel

theorem tot881 : totK PD2M8K2 D2M8K2.t881 = [0, 152199621725, 390480814296, 258117456533, 90515886319, 6784511402, 0, 0] := by
  decide +kernel

theorem rows882 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t882 = true := by
  decide +kernel

theorem tot882 : totK PD2M8K2 D2M8K2.t882 = [0, 176281590438, 466284477084, 250624168906, 19588180468, 0, 0, 0] := by
  decide +kernel

theorem rows883 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t883 = true := by
  decide +kernel

theorem tot883 : totK PD2M8K2 D2M8K2.t883 = [0, 0, 219407553597, 503585558151, 151053890238, 5172807878, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
