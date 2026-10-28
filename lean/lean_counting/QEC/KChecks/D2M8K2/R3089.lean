import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12356 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12356 = true := by
  decide +kernel

theorem tot12356 : totK PD2M8K2 D2M8K2.t12356 = [0, 0, 264593969121, 516033330791, 110754483559, 1198073392, 0, 0] := by
  decide +kernel

theorem rows12357 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12357 = true := by
  decide +kernel

theorem tot12357 : totK PD2M8K2 D2M8K2.t12357 = [0, 54618809271, 234029726493, 401742544216, 162108983756, 11986244008, 0, 0] := by
  decide +kernel

theorem rows12358 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12358 = true := by
  decide +kernel

theorem tot12358 : totK PD2M8K2 D2M8K2.t12358 = [0, 190239784236, 466084203589, 229618394019, 16192212756, 0, 0, 0] := by
  decide +kernel

theorem rows12359 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12359 = true := by
  decide +kernel

theorem tot12359 : totK PD2M8K2 D2M8K2.t12359 = [0, 177086745037, 454334409685, 238898684875, 17104814242, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
