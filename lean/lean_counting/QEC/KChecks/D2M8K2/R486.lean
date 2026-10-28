import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1944 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1944 = true := by
  decide +kernel

theorem tot1944 : totK PD2M8K2 D2M8K2.t1944 = [0, 0, 272123101761, 516807550044, 111486526115, 1369150432, 0, 0] := by
  decide +kernel

theorem rows1945 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1945 = true := by
  decide +kernel

theorem tot1945 : totK PD2M8K2 D2M8K2.t1945 = [0, 157384650155, 434240329001, 295408238060, 29375798609, 0, 0, 0] := by
  decide +kernel

theorem rows1946 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1946 = true := by
  decide +kernel

theorem tot1946 : totK PD2M8K2 D2M8K2.t1946 = [0, 184692093046, 475792881451, 210394148990, 12373752831, 0, 0, 0] := by
  decide +kernel

theorem rows1947 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1947 = true := by
  decide +kernel

theorem tot1947 : totK PD2M8K2 D2M8K2.t1947 = [0, 0, 253298227931, 497067346188, 127924341815, 2309606161, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
